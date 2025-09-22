#include "sse_emu.h"

#ifdef _WIN32
#include <windows.h>
#else
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <signal.h>
#include <stdlib.h>
#include <ucontext.h>
#endif

#include <stdio.h>

/* SSE3 OPS */
static unsigned char OP_ADDSUBPS[] = {0xF2, 0x0F, 0xD0};
static unsigned char OP_ADDSUBPD[] = {0x66, 0x0F, 0xD0};
static unsigned char OP_HADDPS[] = {0xF2, 0x0F, 0x7C};
static unsigned char OP_HADDPD[] = {0x66, 0x0F, 0x7C};
static unsigned char OP_HSUBPS[] = {0xF2, 0x0F, 0x7D};
static unsigned char OP_HSUBPD[] = {0x66, 0x0F, 0x7D};
static unsigned char OP_LDDQU[] = {0xF2, 0x0F, 0xF0};
static unsigned char OP_MOVSLDUP[] = {0xF3, 0x0F, 0x12};
static unsigned char OP_MOVSHDUP[] = {0xF3, 0x0F, 0x16};
static unsigned char OP_MOVDDUP[] = {0xF2, 0x0F, 0x12};
static unsigned char OP_FISTTP16[] = {0xDF};
static unsigned char OP_FISTTP32[] = {0xDB};
static unsigned char OP_FISTTP64[] = {0xDD};
static unsigned char OP_MONITOR[] = {0x0F, 0x01, 0xC8};
static unsigned char OP_MWAIT[] = {0x0F, 0x01, 0x09};
/* SSE2 OPS */
static unsigned char OP_CVTPS2PD[] = {0x0F, 0x5A};
static unsigned char OP_MOVSD_0[] = {0xF2, 0x0F, 0x10};
static unsigned char OP_MOVSD_1[] = {0xF2, 0x0F, 0x11};
static unsigned char OP_CVTTPS2DQ[] = {0xF3, 0x0F, 0x5B};
static unsigned char OP_CVTSI2SD[] = {0xF2, 0x0F, 0x2A};
static unsigned char OP_MULSD[] = {0xF2, 0x0F, 0x59};
static unsigned char OP_XORPD[] = {0x66, 0x0F, 0x57};
static unsigned char OP_CVTTSD2SI[] = {0xF2, 0x0F, 0x2C};
static unsigned char OP_ADDSD[] = {0xF2, 0x0F, 0x58};
static unsigned char OP_CVTPD2PS[] = {0x66, 0x0F, 0x5A};
static unsigned char OP_DIVSD[] = {0xF2, 0x0F, 0x5E};
static unsigned char OP_SUBSD[] = {0xF2, 0x0F, 0x5C};
static unsigned char OP_UCOMISD[] = {0x66, 0x0F, 0x2E};
static unsigned char OP_MOVAPD_0[] = {0x66, 0x0F, 0x28};
static unsigned char OP_MOVAPD_1[] = {0x66, 0x0F, 0x29};

typedef struct {
    int reg;
    int rm;
    int addr;
    int use_address;
    int bytes_used;
} modrm_t;

typedef struct {
    unsigned char data[16];
} xmmreg_t;

int x87_float_decode(unsigned char *src, unsigned char *buf, int buf_len) {
    unsigned int frac_lo = *(unsigned int *)src;
    unsigned int frac_hi = (*(unsigned int *)(&src[4]) & 0x7fffffff) | 0x80000000;
    unsigned int exp = *(unsigned short *)(&src[8]) & 0x7fff;
    int sign = (src[9] >> 7) & 1;
    int unbiased_exp = exp - 0x3fff;
    unsigned int out[2] = {0, 0};
    int i;

    if (!buf || !buf_len || buf_len > 8) {
        return -1;
    }

    if (unbiased_exp >= 0 && unbiased_exp <= 63) {
        int shift = 63 - unbiased_exp;
        if (shift == 0) {
            out[0] = frac_lo;
            out[1] = frac_hi;
        } else if (shift < 32) {
            out[0] = (frac_lo >> shift) | frac_hi << (32 - shift);
            out[1] = frac_hi >> shift;
        } else {
            out[0] = frac_hi >> (shift % 32);
        }
    } else if (unbiased_exp > 63) {
        out[0] = 0xFFFFFFFF;
        out[1] = 0xFFFFFFFF;
    }
    if (sign && unbiased_exp >= 0) {
        for (i = 0; i < buf_len; ++i) {
            buf[i] = ~((unsigned char *)out)[i];
        }
        if (unbiased_exp > 63) {
            buf[buf_len - 1] = 0x80;
        } else {
            for (i = 0; i < buf_len; ++i) {
                buf[i] += 1;
                if (buf[i] != 0) {
                    break;
                }
            }
        }
    } else {
        for (i = 0; i < buf_len; ++i) {
            buf[i] = ((unsigned char *)out)[i];
        }
        if (unbiased_exp > 63) {
            buf[buf_len - 1] = 0x7f;
        }
    }
    return 0;
}

static modrm_t parse_modrm(unsigned char *data, int **regs) {
    modrm_t modrm = {0, 0, 0, 0, 0};
    int disp = 0, mod = 0, scale = 0, index = 0, base = 0, has_sib = 0;
    modrm.rm = data[modrm.bytes_used] & 7;
    modrm.reg = (data[modrm.bytes_used] >> 3) & 7;
    mod = (data[modrm.bytes_used] >> 6) & 3;
    modrm.bytes_used += 1;
    if (mod != 3) {
        modrm.use_address = 1;
        if (modrm.rm == 4) {
            base = data[modrm.bytes_used] & 7;
            index = (data[modrm.bytes_used] >> 3) & 7;
            scale = (data[modrm.bytes_used] >> 6) & 3;
            modrm.bytes_used += 1;
            has_sib = 1;
        }
        if (mod == 1) {
            disp = (signed char)data[modrm.bytes_used];
            modrm.bytes_used += 1;
        } else if (mod == 2 || (mod == 0 && modrm.rm == 5)) {
            unsigned char *tmp = (unsigned char *)&disp;
            tmp[0] = data[modrm.bytes_used++];
            tmp[1] = data[modrm.bytes_used++];
            tmp[2] = data[modrm.bytes_used++];
            tmp[3] = data[modrm.bytes_used++];
        }
        if (has_sib) {
            int scale_map[4] = {1, 2, 4, 8};
            int index_val, base_val;

            index_val = (index != 4) ? *regs[index] : 0;
            base_val = (mod == 0 && base == 5) ? 0 : *regs[base];

            modrm.addr = (scale_map[scale] * index_val) + base_val + disp;
        } else {
            modrm.addr = (mod == 0 && modrm.rm == 5) ? disp : *regs[modrm.rm] + disp;
        }
    }
    return modrm;
}

/* SSE3 instruction emulation */

static void sse3_addsubps_op(float *dest, float *src) {
    dest[0] -= src[0];
    dest[1] += src[1];
    dest[2] -= src[2];
    dest[3] += src[3];
}

static void sse3_addsubpd_op(double *dest, double *src) {
    dest[0] -= src[0];
    dest[1] += src[1];
}

static void sse3_haddps_op(float *dest_src1, float *src2) {
    dest_src1[0] = dest_src1[0] + dest_src1[1];
    dest_src1[1] = dest_src1[2] + dest_src1[3];
    dest_src1[2] = src2[0] + src2[1];
    dest_src1[3] = src2[2] + src2[3];
}

static void sse3_haddpd_op(double *dest_src1, double *src2) {
    dest_src1[0] = dest_src1[0] + dest_src1[1];
    dest_src1[1] = src2[0] + src2[1];
}

static void sse3_hsubps_op(float *dest_src1, float *src2) {
    dest_src1[0] = dest_src1[0] - dest_src1[1];
    dest_src1[1] = dest_src1[2] - dest_src1[3];
    dest_src1[2] = src2[0] - src2[1];
    dest_src1[3] = src2[2] - src2[3];
}

static void sse3_hsubpd_op(double *dest_src1, double *src2) {
    dest_src1[0] = dest_src1[0] - dest_src1[1];
    dest_src1[1] = src2[0] - src2[1];
}

static void sse3_lddqu_op(unsigned char *dest, unsigned char *src) {
    dest[0] = src[0]; dest[1] = src[1]; dest[2] = src[2]; dest[3] = src[3];
    dest[4] = src[4]; dest[5] = src[5]; dest[6] = src[6]; dest[7] = src[7];
    dest[8] = src[8]; dest[9] = src[9]; dest[10] = src[10]; dest[11] = src[11];
    dest[12] = src[12]; dest[13] = src[13]; dest[14] = src[14]; dest[15] = src[15];
}

static void sse3_movsldup_op(float *dest, float *src) {
    dest[0] = src[0];
    dest[1] = src[0];
    dest[2] = src[2];
    dest[3] = src[2];
}

static void sse3_movshdup_op(float *dest, float *src) {
    dest[0] = src[1];
    dest[1] = src[1];
    dest[2] = src[3];
    dest[3] = src[3];
}

static void sse3_movddup_op(double *dest, double *src) {
    dest[0] = src[0];
    dest[1] = src[0];
}

void sse3_fisttp_op(unsigned int *status_word, unsigned int *tag_word, unsigned char *x87_regs, void *dest, int size_bytes) {
    unsigned int top = (*status_word >> 11) & 7;
    unsigned char *reg = &x87_regs[top * 10];

    if (x87_float_decode(reg, dest, size_bytes) != 0) {
        return;
    }
    *tag_word = (*tag_word & ~(3 << (top * 2))) | (3 << (top * 2));
    top = (top + 1) & 7;
    *status_word = (*status_word & ~(7 << 11)) | (top << 11);
}

/* SSE2 instruction emulation */

static void sse2_cvtps2pd_op(double *dest, float *src) {
    dest[0] = (double)src[0];
    dest[1] = (double)src[1];
}

static void sse2_movsd_op(double *dest, double *src, int erase_top) {
    dest[0] = src[0];
    if (erase_top) {
        dest[1] = 0.0;
    }
}

static void sse2_cvttps2dq_op(int *dest, float *src) {
    dest[0] = (int)src[0];
    dest[1] = (int)src[1];
    dest[2] = (int)src[2];
    dest[3] = (int)src[3];
}

static void sse2_cvtsi2sd_op(double *dest, int *src) {
    dest[0] = (double)src[0];
}

static void sse2_mulsd_op(double *dest, double *src) {
    dest[0] *= src[0];
}

static void sse2_xorpd_op(unsigned int *dest, unsigned int *src) {
    dest[0] ^= src[0];
    dest[1] ^= src[1];
    dest[2] ^= src[2];
    dest[3] ^= src[3];
}

static void sse2_cvttsd2si_op(int *dest, double *src) {
    dest[0] = (int)src[0];
}

static void sse2_addsd_op(double *dest, double *src) {
    dest[0] += src[0];
}

static void sse2_cvtpd2ps_op(float *dest, double *src) {
    dest[0] = (float)src[0];
    dest[1] = (float)src[1];
    dest[2] = dest[3] = 0.0;
}

static void sse2_divsd_op(double *dest, double *src) {
    dest[0] /= src[0];
}

static void sse2_subsd_op(double *dest, double *src) {
    dest[0] -= src[0];
}

static void sse2_ucomisd_op(double *dest, double *src, unsigned int *eflags) {
    unsigned int cf = 0, pf = 0, zf = 0;
    unsigned int exp_dest = (((unsigned int *)&dest)[1] >> 20) & 0x7FF;
    unsigned int exp_src = (((unsigned int *)&src)[1] >> 20) & 0x7FF;
    unsigned int frac_hi_dest = ((unsigned int *)&dest)[1] & 0xfffff;
    unsigned int frac_hi_src = ((unsigned int *)&src)[1] & 0xfffff;
    unsigned int frac_lo_dest = ((unsigned int *)&dest)[0];
    unsigned int frac_lo_src = ((unsigned int *)&src)[0];

    if (
        (exp_dest == 0x7FF && (frac_hi_dest != 0 || frac_lo_dest != 0)) ||
        (exp_src == 0x7FF && (frac_hi_src != 0 || frac_lo_src != 0))
    ) {
        cf = 0x0001;
        pf = 0x0004;
        zf = 0x0040;
    } else if (dest[0] == src[0]) {
        zf = 0x0040;
    } else if (dest[0] < src[0]) {
        cf = 0x0001;
    }
    *eflags = (*eflags & ~0x08d5) | cf | pf | zf;
}

static void sse2_movapd_op(double *dest, double *src) {
    dest[0] = src[0];
    dest[1] = src[1];
}

static int run_instruction(unsigned char *data, int *eax, int *ecx, int *edx, int *ebx, int *esp, int *ebp, int *esi, int *edi, unsigned char *fxsave, unsigned int *status_word, unsigned int *tag_word, unsigned char *x87_regs, unsigned int *eflags) {
    int *regs[8];
    regs[0] = eax; regs[1] = ecx;
    regs[2] = edx; regs[3] = ebx;
    regs[4] = esp; regs[5] = ebp;
    regs[6] = esi; regs[7] = edi;
    /* SSE3 handling */
    if (data[0] == OP_ADDSUBPS[0] && data[1] == OP_ADDSUBPS[1] && data[2] == OP_ADDSUBPS[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse3_addsubps_op((float *)xmm_regs[modrm.reg].data, modrm.use_address ? (float *)modrm.addr : (float *)xmm_regs[modrm.rm].data);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_ADDSUBPD[0] && data[1] == OP_ADDSUBPD[1] && data[2] == OP_ADDSUBPD[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse3_addsubpd_op((double *)xmm_regs[modrm.reg].data, modrm.use_address ? (double *)modrm.addr : (double *)xmm_regs[modrm.rm].data);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_HADDPS[0] && data[1] == OP_HADDPS[1] && data[2] == OP_HADDPS[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse3_haddps_op((float *)xmm_regs[modrm.reg].data, modrm.use_address ? (float *)modrm.addr : (float *)xmm_regs[modrm.rm].data);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_HADDPD[0] && data[1] == OP_HADDPD[1] && data[2] == OP_HADDPD[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse3_haddpd_op((double *)xmm_regs[modrm.reg].data, modrm.use_address ? (double *)modrm.addr : (double *)xmm_regs[modrm.rm].data);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_HSUBPS[0] && data[1] == OP_HSUBPS[1] && data[2] == OP_HSUBPS[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse3_hsubps_op((float *)xmm_regs[modrm.reg].data, modrm.use_address ? (float *)modrm.addr : (float *)xmm_regs[modrm.rm].data);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_HSUBPD[0] && data[1] == OP_HSUBPD[1] && data[2] == OP_HSUBPD[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse3_hsubpd_op((double *)xmm_regs[modrm.reg].data, modrm.use_address ? (double *)modrm.addr : (double *)xmm_regs[modrm.rm].data);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_LDDQU[0] && data[1] == OP_LDDQU[1] && data[2] == OP_LDDQU[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        if (modrm.use_address) {
            sse3_lddqu_op(xmm_regs[modrm.reg].data, (unsigned char *)modrm.addr);
        }
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_MOVSLDUP[0] && data[1] == OP_MOVSLDUP[1] && data[2] == OP_MOVSLDUP[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse3_movsldup_op((float *)xmm_regs[modrm.reg].data, modrm.use_address ? (float *)modrm.addr : (float *)xmm_regs[modrm.rm].data);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_MOVSHDUP[0] && data[1] == OP_MOVSHDUP[1] && data[2] == OP_MOVSHDUP[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse3_movshdup_op((float *)xmm_regs[modrm.reg].data, modrm.use_address ? (float *)modrm.addr : (float *)xmm_regs[modrm.rm].data);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_MOVDDUP[0] && data[1] == OP_MOVDDUP[1] && data[2] == OP_MOVDDUP[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse3_movddup_op((double *)xmm_regs[modrm.reg].data, modrm.use_address ? (double *)modrm.addr : (double *)xmm_regs[modrm.rm].data);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_MONITOR[0] && data[1] == OP_MONITOR[1] && data[2] == OP_MONITOR[2]) {
        return 3;
    }
    if (data[0] == OP_MWAIT[0] && data[1] == OP_MWAIT[1] && data[2] == OP_MWAIT[2]) {
        return 3;
    }
    if (data[0] == OP_FISTTP16[0]) {
        modrm_t modrm = parse_modrm(&data[1], regs);
        if (modrm.reg == 1) {
            sse3_fisttp_op(status_word, tag_word, x87_regs, (unsigned char *)modrm.addr, 2);
            return 1 + modrm.bytes_used;
        }
    }
    if (data[0] == OP_FISTTP32[0]) {
        modrm_t modrm = parse_modrm(&data[1], regs);
        if (modrm.reg == 1) {
            sse3_fisttp_op(status_word, tag_word, x87_regs, (unsigned char *)modrm.addr, 4);
            return 1 + modrm.bytes_used;
        }
    }
    if (data[0] == OP_FISTTP64[0]) {
        modrm_t modrm = parse_modrm(&data[1], regs);
        if (modrm.reg == 1) {
            sse3_fisttp_op(status_word, tag_word, x87_regs, (unsigned char *)modrm.addr, 8);
            return 1 + modrm.bytes_used;
        }
    }
    /* SSE2 handling*/
    if (data[0] == OP_CVTPS2PD[0] && data[1] == OP_CVTPS2PD[1]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[2], regs);
        sse2_cvtps2pd_op((double *)xmm_regs[modrm.reg].data, modrm.use_address ? (float *)modrm.addr : (float *)xmm_regs[modrm.rm].data);
        return 2 + modrm.bytes_used;
    }
    if (data[0] == OP_MOVSD_0[0] && data[1] == OP_MOVSD_0[1] && data[2] == OP_MOVSD_0[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse2_movsd_op((double *)xmm_regs[modrm.reg].data, modrm.use_address ? (double *)modrm.addr : (double *)xmm_regs[modrm.rm].data, modrm.use_address);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_MOVSD_1[0] && data[1] == OP_MOVSD_1[1] && data[2] == OP_MOVSD_1[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse2_movsd_op(modrm.use_address ? (double *)modrm.addr : (double *)xmm_regs[modrm.rm].data, (double *)xmm_regs[modrm.reg].data, 0);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_CVTTPS2DQ[0] && data[1] == OP_CVTTPS2DQ[1] && data[2] == OP_CVTTPS2DQ[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse2_cvttps2dq_op((int *)xmm_regs[modrm.reg].data, modrm.use_address ? (float *)modrm.addr : (float *)xmm_regs[modrm.rm].data);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_CVTSI2SD[0] && data[1] == OP_CVTSI2SD[1] && data[2] == OP_CVTSI2SD[2]) {
        xmmreg_t *regs_xmm = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse2_cvtsi2sd_op((double *)regs_xmm[modrm.reg].data, modrm.use_address ? (int *)modrm.addr : regs[modrm.rm]);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_MULSD[0] && data[1] == OP_MULSD[1] && data[2] == OP_MULSD[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse2_mulsd_op((double *)xmm_regs[modrm.reg].data, modrm.use_address ? (double *)modrm.addr : (double *)xmm_regs[modrm.rm].data);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_XORPD[0] && data[1] == OP_XORPD[1] && data[2] == OP_XORPD[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse2_xorpd_op((unsigned int *)xmm_regs[modrm.reg].data, modrm.use_address ? (unsigned int *)modrm.addr : (unsigned int *)xmm_regs[modrm.rm].data);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_CVTTSD2SI[0] && data[1] == OP_CVTTSD2SI[1] && data[2] == OP_CVTTSD2SI[2]) {
        xmmreg_t *regs_xmm = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse2_cvttsd2si_op(regs[modrm.reg], modrm.use_address ? (double *)modrm.addr : (double *)regs_xmm[modrm.rm].data);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_ADDSD[0] && data[1] == OP_ADDSD[1] && data[2] == OP_ADDSD[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse2_addsd_op((double *)xmm_regs[modrm.reg].data, modrm.use_address ? (double *)modrm.addr : (double *)xmm_regs[modrm.rm].data);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_CVTPD2PS[0] && data[1] == OP_CVTPD2PS[1] && data[2] == OP_CVTPD2PS[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse2_cvtpd2ps_op((float *)xmm_regs[modrm.reg].data, modrm.use_address ? (double *)modrm.addr : (double *)xmm_regs[modrm.rm].data);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_DIVSD[0] && data[1] == OP_DIVSD[1] && data[2] == OP_DIVSD[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse2_divsd_op((double *)xmm_regs[modrm.reg].data, modrm.use_address ? (double *)modrm.addr : (double *)xmm_regs[modrm.rm].data);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_SUBSD[0] && data[1] == OP_SUBSD[1] && data[2] == OP_SUBSD[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse2_subsd_op((double *)xmm_regs[modrm.reg].data, modrm.use_address ? (double *)modrm.addr : (double *)xmm_regs[modrm.rm].data);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_UCOMISD[0] && data[1] == OP_UCOMISD[1] && data[2] == OP_UCOMISD[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        sse2_ucomisd_op((double *)xmm_regs[modrm.reg].data, modrm.use_address ? (double *)modrm.addr : (double *)xmm_regs[modrm.rm].data, eflags);
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_MOVAPD_0[0] && data[1] == OP_MOVAPD_0[1] && data[2] == OP_MOVAPD_0[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        if (!(modrm.addr & 0x0f) || !modrm.use_address) {
            sse2_movapd_op((double *)xmm_regs[modrm.reg].data, modrm.use_address ? (double *)modrm.addr : (double *)xmm_regs[modrm.rm].data);
        }
        return 3 + modrm.bytes_used;
    }
    if (data[0] == OP_MOVAPD_1[0] && data[1] == OP_MOVAPD_1[1] && data[2] == OP_MOVAPD_1[2]) {
        xmmreg_t *xmm_regs = (xmmreg_t *)(&fxsave[0xa0]);
        modrm_t modrm = parse_modrm(&data[3], regs);
        if (!(modrm.addr & 0x0f) || !modrm.use_address) {
            sse2_movapd_op(modrm.use_address ? (double *)modrm.addr : (double *)xmm_regs[modrm.rm].data, (double *)xmm_regs[modrm.reg].data);
        }
        return 3 + modrm.bytes_used;
    }
    printf("crash inst: %x %x %x\n", data[0], data[1], data[2]);
    return 0;
}

#ifdef _WIN32
LONG WINAPI sse_emu_exception_handler(EXCEPTION_POINTERS *info) {
    if (info->ExceptionRecord->ExceptionCode == EXCEPTION_ILLEGAL_INSTRUCTION) {
        int len = run_instruction(
            (unsigned char *)info->ContextRecord->Eip,
            (int *)&info->ContextRecord->Eax,
            (int *)&info->ContextRecord->Ecx,
            (int *)&info->ContextRecord->Edx,
            (int *)&info->ContextRecord->Ebx,
            (int *)&info->ContextRecord->Esp,
            (int *)&info->ContextRecord->Ebp,
            (int *)&info->ContextRecord->Esi,
            (int *)&info->ContextRecord->Edi,
            (unsigned char *)info->ContextRecord->ExtendedRegisters,
            (unsigned int *)&info->ContextRecord->FloatSave.StatusWord,
            (unsigned int *)&info->ContextRecord->FloatSave.TagWord,
            (unsigned char *)info->ContextRecord->FloatSave.RegisterArea,
            (unsigned int *)&info->ContextRecord->EFlags
        );
        if (len) {
            info->ContextRecord->Eip += len;
            return EXCEPTION_CONTINUE_EXECUTION;
        }
    }
    return EXCEPTION_CONTINUE_SEARCH;
}

void sse_emu_install_handler() {
    AddVectoredExceptionHandler(1, sse_emu_exception_handler);
}
#else
void sse_emu_exception_handler(int signo, siginfo_t *info, void *context) {
    greg_t *regs = ((ucontext_t *)context)->uc_mcontext.gregs;
    fpregset_t fp_regs = ((ucontext_t *)context)->uc_mcontext.fpregs;
    unsigned char *fxsave = &((unsigned char *)fp_regs)[sizeof(struct _libc_fpstate)];
    int len = run_instruction(
        (unsigned char *)regs[REG_EIP],
        (unsigned int *)&regs[REG_EAX],
        (unsigned int *)&regs[REG_ECX],
        (unsigned int *)&regs[REG_EDX],
        (unsigned int *)&regs[REG_EBX],
        (unsigned int *)&regs[REG_ESP],
        (unsigned int *)&regs[REG_EBP],
        (unsigned int *)&regs[REG_ESI],
        (unsigned int *)&regs[REG_EDI],
        fxsave,
        (unsigned int *)&fp_regs->sw,
        (unsigned int *)&fp_regs->tag,
        (unsigned char *)fp_regs->_st,
        (unsigned int *)&regs[REG_EFL]
    );
    if (len) {
        regs[REG_EIP] += len;
    } else {
        exit(EXIT_FAILURE);
    }
}

void sse3_install_handler() {
    struct sigaction act = {0}, old_act = {0};
    act.sa_sigaction = sse_emu_exception_handler;
    sigaction(SIGILL, &act, &old_act);
}
#endif

