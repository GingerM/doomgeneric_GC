//
// doomgeneric_gc.c - Nintendo GameCube (devkitPPC / libogc) platform layer
//
// Implements the five doomgeneric hooks (+ window title no-op) on top of the
// GX graphics pipeline and the PAD (controller) driver.
//
// Purpose of this first pass: DE-RISK two things independently of the rest of
// the port ---
//   1. the GX blit   : getting DG_ScreenBuffer onto the TV every frame, and
//   2. the PAD mapping: translating GC controller input into DOOM key events.
//
// Everything here is deliberately explicit and heavily commented so the tricky
// parts (RGBA8 texture tiling, pixel byte-order, analog-stick edge detection)
// are easy to inspect and retune.
//
// Copyright(C) 1993-1996 Id Software, Inc. (original DOOM, GPLv2)
// GameCube platform layer: GPLv2, matching the rest of doomgeneric.
//

#include <gccore.h>
#include <ogc/pad.h>
#include <ogc/lwp_watchdog.h>   // gettime(), ticks_to_millisecs()
#include <fat.h>                // fatInitDefault() so DOOM can find the WAD

#include <malloc.h>
#include <string.h>
#include <unistd.h>             // usleep()

#include "doomkeys.h"
#include "doomgeneric.h"

// ---------------------------------------------------------------------------
// Video / GX state
// ---------------------------------------------------------------------------

#define DEFAULT_FIFO_SIZE (256 * 1024)

static void        *s_xfb[2]  = { NULL, NULL }; // external framebuffers (double buffered)
static u32          s_fbIndex = 0;
static GXRModeObj  *s_rmode   = NULL;
static void        *s_fifo    = NULL;

// The DOOM frame is uploaded as a single GX texture in RGBA8 (tiled) format.
// GX_TF_RGBA8 tiles are 4x4 texels, so the dimensions must be multiples of 4.
// Default doomgeneric res is 640x400, both divisible by 4. Guard it anyway.
#if (DOOMGENERIC_RESX % 4) || (DOOMGENERIC_RESY % 4)
#error "GX_TF_RGBA8 requires DOOMGENERIC_RESX/RESY to be multiples of 4"
#endif

static u8      *s_texData = NULL;   // 32-byte aligned, tiled RGBA8 texels
static GXTexObj s_texObj;

// ---------------------------------------------------------------------------
// Input: key event ring buffer (same pattern the other ports use)
// ---------------------------------------------------------------------------

#define KEYQUEUE_SIZE 16

static unsigned short s_keyQueue[KEYQUEUE_SIZE];
static unsigned int   s_keyWrite = 0;
static unsigned int   s_keyRead  = 0;

static void queueKey(int pressed, unsigned char doomKey)
{
    // High byte = pressed flag, low byte = DOOM key code.
    s_keyQueue[s_keyWrite] = (unsigned short)((pressed << 8) | doomKey);
    s_keyWrite = (s_keyWrite + 1) % KEYQUEUE_SIZE;
}

// ---------------------------------------------------------------------------
// GX blit: convert DG_ScreenBuffer -> tiled RGBA8 texture
// ---------------------------------------------------------------------------
//
// Pixel byte-order note (the subtle bit, verified on hardware):
//   i_video.c packs each pixel as 0x00RRGGBB. On this big-endian target the
//   framebuffer ends up stored in ARGB order, so in ascending address order
//   the bytes are:  [0]=x(pad)  [1]=R  [2]=G  [3]=B.
//   (An earlier guess of [B,G,R,x] produced a green/yellow image with no blue
//   -- grays came out yellow -- which is how this was pinned down.)
//   We read through a byte pointer so this is independent of how the compiler
//   would interpret the 32-bit word.
//
// GX_TF_RGBA8 tile layout (per 4x4 block = 64 bytes):
//   bytes  0..31 : sixteen (A,R) pairs   -> [2*i]=A, [2*i+1]=R
//   bytes 32..63 : sixteen (G,B) pairs   -> [32+2*i]=G, [32+2*i+1]=B
//   where i = (py*4 + px) walks the block in row-major order.
//
static void blitFrameToTexture(void)
{
    const pixel_t *src = DG_ScreenBuffer;
    u8            *dst = s_texData;      // advances one 64-byte tile at a time
    const int      w   = DOOMGENERIC_RESX;
    const int      h   = DOOMGENERIC_RESY;

    for (int ty = 0; ty < h; ty += 4)
    {
        for (int tx = 0; tx < w; tx += 4)
        {
            for (int py = 0; py < 4; py++)
            {
                for (int px = 0; px < 4; px++)
                {
                    const u8 *p = (const u8 *)&src[(ty + py) * w + (tx + px)];
                    // Memory order is [x, R, G, B]; p[0] is the unused pad byte.
                    const u8  r = p[1];
                    const u8  g = p[2];
                    const u8  b = p[3];

                    const int i = (py * 4 + px);
                    dst[i * 2 + 0]      = 0xFF; // A
                    dst[i * 2 + 1]      = r;    // R
                    dst[32 + i * 2 + 0] = g;    // G
                    dst[32 + i * 2 + 1] = b;    // B
                }
            }
            dst += 64; // next 4x4 tile
        }
    }

    // The texture lives in main RAM; flush the CPU cache so GX (which reads
    // through the memory bus, not the CPU cache) sees the fresh bytes.
    DCFlushRange(s_texData, w * h * 4);
}

// ---------------------------------------------------------------------------
// PAD mapping
// ---------------------------------------------------------------------------
//
// Control scheme (retune freely):
//   A            -> Fire
//   B            -> Use / open doors
//   X            -> Enter (menu confirm)
//   Y            -> Automap (Tab)
//   L trigger    -> Strafe left
//   R trigger    -> Strafe right
//   Z            -> Run modifier (Shift, held)
//   Start        -> Escape / menu
//   D-pad        -> Arrow keys (menu + move/turn)
//   Left stick X -> Turn left / right
//   Left stick Y -> Move forward / back
//
// Digital buttons use PAD_ButtonsDown()/PAD_ButtonsUp() for clean press/release
// edges. The analog stick is thresholded into virtual buttons and we track the
// previous state so we only emit an edge when it crosses the deadzone.

#define STICK_DEADZONE 40   // GC stick range is roughly -128..127

typedef struct { u32 mask; unsigned char key; } PadBinding;

static const PadBinding s_padBindings[] = {
    { PAD_BUTTON_A,     KEY_FIRE       },
    { PAD_BUTTON_B,     KEY_USE        },
    { PAD_BUTTON_X,     KEY_ENTER      },
    { PAD_BUTTON_Y,     KEY_TAB        },
    { PAD_TRIGGER_L,    KEY_STRAFE_L   },
    { PAD_TRIGGER_R,    KEY_STRAFE_R   },
    { PAD_TRIGGER_Z,    KEY_RSHIFT     },
    { PAD_BUTTON_START, KEY_ESCAPE     },
    { PAD_BUTTON_UP,    KEY_UPARROW    },
    { PAD_BUTTON_DOWN,  KEY_DOWNARROW  },
    { PAD_BUTTON_LEFT,  KEY_LEFTARROW  },
    { PAD_BUTTON_RIGHT, KEY_RIGHTARROW },
};
#define NUM_PAD_BINDINGS (sizeof(s_padBindings) / sizeof(s_padBindings[0]))

// Previous analog-derived direction state, for edge detection.
static int s_prevStickLeft  = 0;
static int s_prevStickRight = 0;
static int s_prevStickUp    = 0;
static int s_prevStickDown  = 0;

static void emitStickEdge(int nowActive, int *prevActive, unsigned char key)
{
    if (nowActive && !*prevActive)      queueKey(1, key);
    else if (!nowActive && *prevActive) queueKey(0, key);
    *prevActive = nowActive;
}

static void handlePad(void)
{
    PAD_ScanPads();

    const u32 down = PAD_ButtonsDown(0);
    const u32 up   = PAD_ButtonsUp(0);

    for (unsigned int i = 0; i < NUM_PAD_BINDINGS; i++)
    {
        if (down & s_padBindings[i].mask) queueKey(1, s_padBindings[i].key);
        if (up   & s_padBindings[i].mask) queueKey(0, s_padBindings[i].key);
    }

    // Left analog stick -> turn (X) and move (Y). GC Y is +up.
    const s8 sx = PAD_StickX(0);
    const s8 sy = PAD_StickY(0);

    emitStickEdge(sx < -STICK_DEADZONE, &s_prevStickLeft,  KEY_LEFTARROW);
    emitStickEdge(sx >  STICK_DEADZONE, &s_prevStickRight, KEY_RIGHTARROW);
    emitStickEdge(sy >  STICK_DEADZONE, &s_prevStickUp,    KEY_UPARROW);
    emitStickEdge(sy < -STICK_DEADZONE, &s_prevStickDown,  KEY_DOWNARROW);
}

// ---------------------------------------------------------------------------
// doomgeneric hooks
// ---------------------------------------------------------------------------

void DG_Init(void)
{
    memset(s_keyQueue, 0, sizeof(s_keyQueue));

    // --- Video / XFB setup ---
    VIDEO_Init();
    PAD_Init();

    s_rmode = VIDEO_GetPreferredMode(NULL);

    s_xfb[0] = MEM_K0_TO_K1(SYS_AllocateFramebuffer(s_rmode));
    s_xfb[1] = MEM_K0_TO_K1(SYS_AllocateFramebuffer(s_rmode));

    VIDEO_Configure(s_rmode);
    VIDEO_SetNextFramebuffer(s_xfb[s_fbIndex]);
    VIDEO_SetBlack(FALSE);
    VIDEO_Flush();
    VIDEO_WaitVSync();
    if (s_rmode->viTVMode & VI_NON_INTERLACE) VIDEO_WaitVSync();

    // --- GX setup ---
    s_fifo = memalign(32, DEFAULT_FIFO_SIZE);
    memset(s_fifo, 0, DEFAULT_FIFO_SIZE);
    GX_Init(s_fifo, DEFAULT_FIFO_SIZE);

    GXColor bg = { 0, 0, 0, 0xFF };
    GX_SetCopyClear(bg, GX_MAX_Z24);

    GX_SetViewport(0, 0, s_rmode->fbWidth, s_rmode->efbHeight, 0, 1);
    f32 yscale    = GX_GetYScaleFactor(s_rmode->efbHeight, s_rmode->xfbHeight);
    u32 xfbHeight = GX_SetDispCopyYScale(yscale);
    GX_SetScissor(0, 0, s_rmode->fbWidth, s_rmode->efbHeight);
    GX_SetDispCopySrc(0, 0, s_rmode->fbWidth, s_rmode->efbHeight);
    GX_SetDispCopyDst(s_rmode->fbWidth, xfbHeight);
    GX_SetCopyFilter(s_rmode->aa, s_rmode->sample_pattern, GX_TRUE, s_rmode->vfilter);
    GX_SetFieldMode(s_rmode->field_rendering,
                    ((s_rmode->viHeight == 2 * s_rmode->xfbHeight) ? GX_ENABLE : GX_DISABLE));

    GX_SetPixelFmt((s_rmode->aa) ? GX_PF_RGB565_Z16 : GX_PF_RGB8_Z24, GX_ZC_LINEAR);

    GX_SetCullMode(GX_CULL_NONE);
    GX_CopyDisp(s_xfb[s_fbIndex], GX_TRUE);
    GX_SetDispCopyGamma(GX_GM_1_0);

    // Vertex format 0: 2D position + 2D texcoord, both float.
    GX_ClearVtxDesc();
    GX_SetVtxDesc(GX_VA_POS,  GX_DIRECT);
    GX_SetVtxDesc(GX_VA_TEX0, GX_DIRECT);
    GX_SetVtxAttrFmt(GX_VTXFMT0, GX_VA_POS,  GX_POS_XY, GX_F32, 0);
    GX_SetVtxAttrFmt(GX_VTXFMT0, GX_VA_TEX0, GX_TEX_ST, GX_F32, 0);

    // Single TEV stage that just replaces with the texture color.
    GX_SetNumChans(1);
    GX_SetNumTexGens(1);
    GX_SetTevOp(GX_TEVSTAGE0, GX_REPLACE);
    GX_SetTevOrder(GX_TEVSTAGE0, GX_TEXCOORD0, GX_TEXMAP0, GX_COLORNULL);
    GX_SetTexCoordGen(GX_TEXCOORD0, GX_TG_MTX2x4, GX_TG_TEX0, GX_IDENTITY);

    // Orthographic projection: screen-space pixels, origin top-left,
    // +Y downwards so it lines up with the DOOM framebuffer row order.
    Mtx44 proj;
    guOrtho(proj, 0, DOOMGENERIC_RESY, 0, DOOMGENERIC_RESX, 0, 300);
    GX_LoadProjectionMtx(proj, GX_ORTHOGRAPHIC);

    Mtx mv;
    guMtxIdentity(mv);
    guMtxTransApply(mv, mv, 0.0F, 0.0F, -5.0F);
    GX_LoadPosMtxImm(mv, GX_PNMTX0);

    // --- Texture ---
    s_texData = (u8 *)memalign(32, DOOMGENERIC_RESX * DOOMGENERIC_RESY * 4);
    memset(s_texData, 0, DOOMGENERIC_RESX * DOOMGENERIC_RESY * 4);
    GX_InitTexObj(&s_texObj, s_texData,
                  DOOMGENERIC_RESX, DOOMGENERIC_RESY,
                  GX_TF_RGBA8, GX_CLAMP, GX_CLAMP, GX_FALSE);
    // Nearest filtering keeps the low-res DOOM image crisp rather than blurry.
    GX_InitTexObjFilterMode(&s_texObj, GX_NEAR, GX_NEAR);
}

void DG_DrawFrame(void)
{
    // 1. Poll input (edges are queued for DG_GetKey to drain).
    handlePad();

    // 2. Upload the finished DOOM frame as a texture.
    blitFrameToTexture();
    GX_LoadTexObj(&s_texObj, GX_TEXMAP0);
    GX_InvalidateTexAll();

    // 3. Draw a single fullscreen textured quad (screen-space coords).
    GX_SetViewport(0, 0, s_rmode->fbWidth, s_rmode->efbHeight, 0, 1);

    GX_Begin(GX_QUADS, GX_VTXFMT0, 4);
        GX_Position2f32(0.0f,             0.0f);              GX_TexCoord2f32(0.0f, 0.0f);
        GX_Position2f32(DOOMGENERIC_RESX, 0.0f);              GX_TexCoord2f32(1.0f, 0.0f);
        GX_Position2f32(DOOMGENERIC_RESX, DOOMGENERIC_RESY);  GX_TexCoord2f32(1.0f, 1.0f);
        GX_Position2f32(0.0f,             DOOMGENERIC_RESY);  GX_TexCoord2f32(0.0f, 1.0f);
    GX_End();

    // 4. Resolve EFB -> the next XFB and flip.
    GX_DrawDone();

    s_fbIndex ^= 1;
    GX_SetZMode(GX_TRUE, GX_LEQUAL, GX_TRUE);
    GX_SetColorUpdate(GX_TRUE);
    GX_CopyDisp(s_xfb[s_fbIndex], GX_TRUE);

    VIDEO_SetNextFramebuffer(s_xfb[s_fbIndex]);
    VIDEO_Flush();
    VIDEO_WaitVSync();
}

void DG_SleepMs(uint32_t ms)
{
    usleep(ms * 1000);
}

uint32_t DG_GetTicksMs(void)
{
    // gettime() is the 64-bit CPU timebase; convert to ms.
    return (uint32_t)ticks_to_millisecs(gettime());
}

int DG_GetKey(int *pressed, unsigned char *doomKey)
{
    if (s_keyRead == s_keyWrite)
        return 0; // queue empty

    const unsigned short keyData = s_keyQueue[s_keyRead];
    s_keyRead = (s_keyRead + 1) % KEYQUEUE_SIZE;

    *pressed = keyData >> 8;
    *doomKey = keyData & 0xFF;
    return 1;
}

void DG_SetWindowTitle(const char *title)
{
    (void)title; // no window on a console
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

int main(int argc, char **argv)
{
    // Mount SD/DVD (via Swiss/SD Gecko/etc.) so DOOM can read the WAD.
    fatInitDefault();

    // This fork searches ONLY the current directory for the IWAD
    // (config.h: FILES_DIR="."). Swiss doesn't guarantee what the working
    // directory is at launch, so chdir() to the folder that holds this .dol
    // (derived from argv[0]). Result: just drop DOOM1.WAD next to the .dol.
    if (argc > 0 && argv[0] != NULL)
    {
        char dir[256];
        strncpy(dir, argv[0], sizeof(dir) - 1);
        dir[sizeof(dir) - 1] = '\0';

        char *slash = strrchr(dir, '/');
        if (slash == NULL) slash = strrchr(dir, '\\');
        if (slash != NULL)
        {
            *slash = '\0';   // strip the executable filename
            chdir(dir);
        }
    }

    doomgeneric_Create(argc, argv);

    while (1)
    {
        doomgeneric_Tick();
    }

    return 0;
}
