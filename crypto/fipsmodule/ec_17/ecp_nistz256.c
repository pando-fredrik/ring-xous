/* Copyright (c) 2014, Intel Corporation.
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
 * OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
 * CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE. */

/* Developers and authors:
 * Shay Gueron (1, 2), and Vlad Krasnov (1)
 * (1) Intel Corporation, Israel Development Center
 * (2) University of Haifa
 * Reference:
 *   Shay Gueron and Vlad Krasnov
 *   "Fast Prime Field Elliptic Curve Cryptography with 256 Bit Primes"
 *   http://eprint.iacr.org/2013/816 */

#include "ecp_nistz256.h"

#include "ecp_nistz.h"
#include "../bn/internal.h"
#include "../../limbs/limbs.inl"

#if defined(__GNUC__)
#pragma GCC diagnostic ignored "-Wsign-conversion"
#endif

/* Functions implemented in assembly */
void GFp_nistz256_neg(Limb res[P256_LIMBS], const Limb a[P256_LIMBS]);

/* One converted into the Montgomery domain */
static const Limb ONE[P256_LIMBS] = {
    TOBN(0x00000000, 0x00000001), TOBN(0xffffffff, 0x00000000),
    TOBN(0xffffffff, 0xffffffff), TOBN(0x00000000, 0xfffffffe),
};

static void copy_conditional(Limb dst[P256_LIMBS],
                             const Limb src[P256_LIMBS], Limb move) {
  Limb mask1 = move;
  Limb mask2 = ~mask1;

  dst[0] = (src[0] & mask1) ^ (dst[0] & mask2);
  dst[1] = (src[1] & mask1) ^ (dst[1] & mask2);
  dst[2] = (src[2] & mask1) ^ (dst[2] & mask2);
  dst[3] = (src[3] & mask1) ^ (dst[3] & mask2);
  if (P256_LIMBS == 8) {
    dst[4] = (src[4] & mask1) ^ (dst[4] & mask2);
    dst[5] = (src[5] & mask1) ^ (dst[5] & mask2);
    dst[6] = (src[6] & mask1) ^ (dst[6] & mask2);
    dst[7] = (src[7] & mask1) ^ (dst[7] & mask2);
  }
}

void GFp_nistz256_point_double(P256_POINT *r, const P256_POINT *a);

#if defined(GFp_USE_LARGE_TABLE)
void GFp_nistz256_point_add_affine(P256_POINT *r, const P256_POINT *a,
                                   const P256_POINT_AFFINE *b);
#endif

void GFp_nistz256_point_add(P256_POINT *r, const P256_POINT *a,
                            const P256_POINT *b);

// |GFp_nistz256_point_add| is defined in assembly language in X86-64 only.
#if !defined(OPENSSL_X86_64)

static const BN_ULONG Q[P256_LIMBS] = {
  TOBN(0xffffffff, 0xffffffff),
  TOBN(0x00000000, 0xffffffff),
  TOBN(0x00000000, 0x00000000),
  TOBN(0xffffffff, 0x00000001),
};

static inline Limb is_equal(const Limb a[P256_LIMBS], const Limb b[P256_LIMBS]) {
  return LIMBS_equal(a, b, P256_LIMBS);
}

static inline Limb is_zero(const BN_ULONG a[P256_LIMBS]) {
  return LIMBS_are_zero(a, P256_LIMBS);
}

static inline void elem_mul_by_2(Limb r[P256_LIMBS], const Limb a[P256_LIMBS]) {
  LIMBS_shl_mod(r, a, Q, P256_LIMBS);
}

static inline void elem_mul_mont(Limb r[P256_LIMBS], const Limb a[P256_LIMBS],
                                 const Limb b[P256_LIMBS]) {
  GFp_nistz256_mul_mont(r, a, b);
}

static inline void elem_sqr_mont(Limb r[P256_LIMBS], const Limb a[P256_LIMBS]) {
  GFp_nistz256_sqr_mont(r, a);
}

static inline void elem_sub(Limb r[P256_LIMBS], const Limb a[P256_LIMBS],
                            const Limb b[P256_LIMBS]) {
  LIMBS_sub_mod(r, a, b, Q, P256_LIMBS);
}

/* Point addition: r = a+b */
void GFp_nistz256_point_add(P256_POINT *r, const P256_POINT *a, const P256_POINT *b) {
  BN_ULONG U2[P256_LIMBS], S2[P256_LIMBS];
  BN_ULONG U1[P256_LIMBS], S1[P256_LIMBS];
  BN_ULONG Z1sqr[P256_LIMBS];
  BN_ULONG Z2sqr[P256_LIMBS];
  BN_ULONG H[P256_LIMBS], R[P256_LIMBS];
  BN_ULONG Hsqr[P256_LIMBS];
  BN_ULONG Rsqr[P256_LIMBS];
  BN_ULONG Hcub[P256_LIMBS];

  BN_ULONG res_x[P256_LIMBS];
  BN_ULONG res_y[P256_LIMBS];
  BN_ULONG res_z[P256_LIMBS];

  const BN_ULONG *in1_x = a->X;
  const BN_ULONG *in1_y = a->Y;
  const BN_ULONG *in1_z = a->Z;

  const BN_ULONG *in2_x = b->X;
  const BN_ULONG *in2_y = b->Y;
  const BN_ULONG *in2_z = b->Z;

  BN_ULONG in1infty = is_zero(a->Z);
  BN_ULONG in2infty = is_zero(b->Z);

  elem_sqr_mont(Z2sqr, in2_z); /* Z2^2 */
  elem_sqr_mont(Z1sqr, in1_z); /* Z1^2 */

  elem_mul_mont(S1, Z2sqr, in2_z); /* S1 = Z2^3 */
  elem_mul_mont(S2, Z1sqr, in1_z); /* S2 = Z1^3 */

  elem_mul_mont(S1, S1, in1_y); /* S1 = Y1*Z2^3 */
  elem_mul_mont(S2, S2, in2_y); /* S2 = Y2*Z1^3 */
  elem_sub(R, S2, S1);          /* R = S2 - S1 */

  elem_mul_mont(U1, in1_x, Z2sqr); /* U1 = X1*Z2^2 */
  elem_mul_mont(U2, in2_x, Z1sqr); /* U2 = X2*Z1^2 */
  elem_sub(H, U2, U1);             /* H = U2 - U1 */

  BN_ULONG is_exceptional = is_equal(U1, U2) & ~in1infty & ~in2infty;
  if (is_exceptional) {
    if (is_equal(S1, S2)) {
      GFp_nistz256_point_double(r, a);
    } else {
      limbs_zero(r->X, P256_LIMBS);
      limbs_zero(r->Y, P256_LIMBS);
      limbs_zero(r->Z, P256_LIMBS);
    }
    return;
  }

  elem_sqr_mont(Rsqr, R);             /* R^2 */
  elem_mul_mont(res_z, H, in1_z);     /* Z3 = H*Z1*Z2 */
  elem_sqr_mont(Hsqr, H);             /* H^2 */
  elem_mul_mont(res_z, res_z, in2_z); /* Z3 = H*Z1*Z2 */
  elem_mul_mont(Hcub, Hsqr, H);       /* H^3 */

  elem_mul_mont(U2, U1, Hsqr); /* U1*H^2 */
  elem_mul_by_2(Hsqr, U2);     /* 2*U1*H^2 */

  elem_sub(res_x, Rsqr, Hsqr);
  elem_sub(res_x, res_x, Hcub);

  elem_sub(res_y, U2, res_x);

  elem_mul_mont(S2, S1, Hcub);
  elem_mul_mont(res_y, R, res_y);
  elem_sub(res_y, res_y, S2);

  copy_conditional(res_x, in2_x, in1infty);
  copy_conditional(res_y, in2_y, in1infty);
  copy_conditional(res_z, in2_z, in1infty);

  copy_conditional(res_x, in1_x, in2infty);
  copy_conditional(res_y, in1_y, in2infty);
  copy_conditional(res_z, in1_z, in2infty);

  limbs_copy(r->X, res_x, P256_LIMBS);
  limbs_copy(r->Y, res_y, P256_LIMBS);
  limbs_copy(r->Z, res_z, P256_LIMBS);
}
#endif

/* r = p * p_scalar */
#if 0
void GFp_nistz256_point_mul(P256_POINT *r, const Limb p_scalar[P256_LIMBS],
                            const Limb p_x[P256_LIMBS],
                            const Limb p_y[P256_LIMBS]) {
  static const size_t kWindowSize = 5;
  static const crypto_word kMask = (1 << (5 /* kWindowSize */ + 1)) - 1;

  uint8_t p_str[(P256_LIMBS * sizeof(Limb)) + 1];
  gfp_little_endian_bytes_from_scalar(p_str, sizeof(p_str) / sizeof(p_str[0]),
                                      p_scalar, P256_LIMBS);

  /* A |P256_POINT| is (3 * 32) = 96 bytes, and the 64-byte alignment should
   * add no more than 63 bytes of overhead. Thus, |table| should require
   * ~1599 ((96 * 16) + 63) bytes of stack space. */
  alignas(64) P256_POINT table[16];

  /* table[0] is implicitly (0,0,0) (the point at infinity), therefore it is
   * not stored. All other values are actually stored with an offset of -1 in
   * table. */
  P256_POINT *row = table;

  limbs_copy(row[1 - 1].X, p_x, P256_LIMBS);
  limbs_copy(row[1 - 1].Y, p_y, P256_LIMBS);
  limbs_copy(row[1 - 1].Z, ONE, P256_LIMBS);

  GFp_nistz256_point_double(&row[2 - 1], &row[1 - 1]);
  GFp_nistz256_point_add(&row[3 - 1], &row[2 - 1], &row[1 - 1]);
  GFp_nistz256_point_double(&row[4 - 1], &row[2 - 1]);
  GFp_nistz256_point_double(&row[6 - 1], &row[3 - 1]);
  GFp_nistz256_point_double(&row[8 - 1], &row[4 - 1]);
  GFp_nistz256_point_double(&row[12 - 1], &row[6 - 1]);
  GFp_nistz256_point_add(&row[5 - 1], &row[4 - 1], &row[1 - 1]);
  GFp_nistz256_point_add(&row[7 - 1], &row[6 - 1], &row[1 - 1]);
  GFp_nistz256_point_add(&row[9 - 1], &row[8 - 1], &row[1 - 1]);
  GFp_nistz256_point_add(&row[13 - 1], &row[12 - 1], &row[1 - 1]);
  GFp_nistz256_point_double(&row[14 - 1], &row[7 - 1]);
  GFp_nistz256_point_double(&row[10 - 1], &row[5 - 1]);
  GFp_nistz256_point_add(&row[15 - 1], &row[14 - 1], &row[1 - 1]);
  GFp_nistz256_point_add(&row[11 - 1], &row[10 - 1], &row[1 - 1]);
  GFp_nistz256_point_double(&row[16 - 1], &row[8 - 1]);

  Limb tmp[P256_LIMBS];
  alignas(32) P256_POINT h;
  static const size_t START_INDEX = 256 - 1;
  size_t index = START_INDEX;

  crypto_word raw_wvalue;
  crypto_word recoded_is_negative;
  crypto_word recoded;

  raw_wvalue = p_str[(index - 1) / 8];
  raw_wvalue = (raw_wvalue >> ((index - 1) % 8)) & kMask;
  booth_recode(&recoded_is_negative, &recoded, raw_wvalue, kWindowSize);
  dev_assert_secret(!recoded_is_negative);
  GFp_nistz256_select_w5(r, table, recoded);

  while (index >= kWindowSize) {
    if (index != START_INDEX) {
      size_t off = (index - 1) / 8;

      raw_wvalue = p_str[off] | p_str[off + 1] << 8;
      raw_wvalue = (raw_wvalue >> ((index - 1) % 8)) & kMask;
      booth_recode(&recoded_is_negative, &recoded, raw_wvalue, kWindowSize);

      GFp_nistz256_select_w5(&h, table, recoded);
      GFp_nistz256_neg(tmp, h.Y);
      copy_conditional(h.Y, tmp, recoded_is_negative);

      GFp_nistz256_point_add(r, r, &h);
    }

    index -= kWindowSize;

    GFp_nistz256_point_double(r, r);
    GFp_nistz256_point_double(r, r);
    GFp_nistz256_point_double(r, r);
    GFp_nistz256_point_double(r, r);
    GFp_nistz256_point_double(r, r);
  }

  /* Final window */
  raw_wvalue = p_str[0];
  raw_wvalue = (raw_wvalue << 1) & kMask;

  booth_recode(&recoded_is_negative, &recoded, raw_wvalue, kWindowSize);
  GFp_nistz256_select_w5(&h, table, recoded);
  GFp_nistz256_neg(tmp, h.Y);
  copy_conditional(h.Y, tmp, recoded_is_negative);
  GFp_nistz256_point_add(r, r, &h);
}
#endif
#if defined(GFp_USE_LARGE_TABLE)

/* Precomputed tables for the default generator */
#include "ecp_nistz256_table.inl"

static const size_t kWindowSize = 7;

static inline void select_precomputed(P256_POINT_AFFINE *p, size_t i,
                                      crypto_word raw_wvalue) {
  crypto_word recoded_is_negative;
  crypto_word recoded;
  booth_recode(&recoded_is_negative, &recoded, raw_wvalue, kWindowSize);
  GFp_nistz256_select_w7(p, GFp_nistz256_precomputed[i], recoded);
  Limb neg_y[P256_LIMBS];
  GFp_nistz256_neg(neg_y, p->Y);
  copy_conditional(p->Y, neg_y, recoded_is_negative);
}

/* This assumes that |x| and |y| have been each been reduced to their minimal
 * unique representations. */
static Limb is_infinity(const Limb x[P256_LIMBS],
                            const Limb y[P256_LIMBS]) {
  Limb acc = 0;
  for (size_t i = 0; i < P256_LIMBS; ++i) {
    acc |= x[i] | y[i];
  }
  return constant_time_is_zero_w(acc);
}
#if 0
void GFp_nistz256_point_mul_base(P256_POINT *r,
                                 const Limb g_scalar[P256_LIMBS]) {
  static const crypto_word kMask = (1 << (7 /* kWindowSize */ + 1)) - 1;

  uint8_t p_str[(P256_LIMBS * sizeof(Limb)) + 1];
  gfp_little_endian_bytes_from_scalar(p_str, sizeof(p_str) / sizeof(p_str[0]),
                                      g_scalar, P256_LIMBS);

  /* First window */
  size_t index = kWindowSize;

  alignas(32) P256_POINT_AFFINE t;

  crypto_word raw_wvalue = (p_str[0] << 1) & kMask;
  select_precomputed(&t, 0, raw_wvalue);

  alignas(32) P256_POINT p;
  limbs_copy(p.X, t.X, P256_LIMBS);
  limbs_copy(p.Y, t.Y, P256_LIMBS);
  limbs_copy(p.Z, ONE, P256_LIMBS);
  /* If it is at the point at infinity then p.p.X will be zero. */
  copy_conditional(p.Z, p.X, is_infinity(p.X, p.Y));

  for (size_t i = 1; i < 37; i++) {
    size_t off = (index - 1) / 8;
    raw_wvalue = p_str[off] | p_str[off + 1] << 8;
    raw_wvalue = (raw_wvalue >> ((index - 1) % 8)) & kMask;
    index += kWindowSize;
    select_precomputed(&t, i, raw_wvalue);
    GFp_nistz256_point_add_affine(&p, &p, &t);
  }

  limbs_copy(r->X, p.X, P256_LIMBS);
  limbs_copy(r->Y, p.Y, P256_LIMBS);
  limbs_copy(r->Z, p.Z, P256_LIMBS);
}
#endif
#endif

#include "p256_32.h"

#define FIAT_P256_NLIMBS 8
typedef uint32_t fiat_p256_limb_t;
typedef uint32_t fiat_p256_felem[FIAT_P256_NLIMBS];
static const fiat_p256_felem fiat_p256_one = {
    0x1, 0x0, 0x0, 0xffffffff, 0xffffffff, 0xffffffff, 0xfffffffe, 0x0};


static fiat_p256_limb_t fiat_p256_nz(
    const fiat_p256_limb_t in1[FIAT_P256_NLIMBS]) {
  fiat_p256_limb_t ret;
  fiat_p256_nonzero(&ret, in1);
  return ret;
}

static void fiat_p256_copy(fiat_p256_limb_t out[FIAT_P256_NLIMBS],
                           const fiat_p256_limb_t in1[FIAT_P256_NLIMBS]) {
  for (size_t i = 0; i < FIAT_P256_NLIMBS; i++) {
    out[i] = in1[i];
  }
}

static void fiat_p256_cmovznz(fiat_p256_limb_t out[FIAT_P256_NLIMBS],
                              fiat_p256_limb_t t,
                              const fiat_p256_limb_t z[FIAT_P256_NLIMBS],
                              const fiat_p256_limb_t nz[FIAT_P256_NLIMBS]) {
  fiat_p256_selectznz(out, !!t, z, nz);
}

// Group operations
// ----------------
//
// Building on top of the field operations we have the operations on the
// elliptic curve group itself. Points on the curve are represented in Jacobian
// coordinates.
//
// Both operations were transcribed to Coq and proven to correspond to naive
// implementations using Affine coordinates, for all suitable fields.  In the
// Coq proofs, issues of constant-time execution and memory layout (aliasing)
// conventions were not considered. Specification of affine coordinates:
// <https://github.com/mit-plv/fiat-crypto/blob/79f8b5f39ed609339f0233098dee1a3c4e6b3080/src/Spec/WeierstrassCurve.v#L28>
// As a sanity check, a proof that these points form a commutative group:
// <https://github.com/mit-plv/fiat-crypto/blob/79f8b5f39ed609339f0233098dee1a3c4e6b3080/src/Curves/Weierstrass/AffineProofs.v#L33>

// fiat_p256_point_double calculates 2*(x_in, y_in, z_in)
//
// The method is taken from:
//   http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-3.html#doubling-dbl-2001-b
//
// Coq transcription and correctness proof:
// <https://github.com/mit-plv/fiat-crypto/blob/79f8b5f39ed609339f0233098dee1a3c4e6b3080/src/Curves/Weierstrass/Jacobian.v#L93>
// <https://github.com/mit-plv/fiat-crypto/blob/79f8b5f39ed609339f0233098dee1a3c4e6b3080/src/Curves/Weierstrass/Jacobian.v#L201>
//
// Outputs can equal corresponding inputs, i.e., x_out == x_in is allowed.
// while x_out == y_in is not (maybe this works, but it's not tested).
void fiat_p256_point_double(fiat_p256_felem x_out, fiat_p256_felem y_out,
                                   fiat_p256_felem z_out,
                                   const fiat_p256_felem x_in,
                                   const fiat_p256_felem y_in,
                                   const fiat_p256_felem z_in) {
  fiat_p256_felem delta, gamma, beta, ftmp, ftmp2, tmptmp, alpha, fourbeta;
  // delta = z^2
  fiat_p256_square(delta, z_in);
  // gamma = y^2
  fiat_p256_square(gamma, y_in);
  // beta = x*gamma
  fiat_p256_mul(beta, x_in, gamma);

  // alpha = 3*(x-delta)*(x+delta)
  fiat_p256_sub(ftmp, x_in, delta);
  fiat_p256_add(ftmp2, x_in, delta);

  fiat_p256_add(tmptmp, ftmp2, ftmp2);
  fiat_p256_add(ftmp2, ftmp2, tmptmp);
  fiat_p256_mul(alpha, ftmp, ftmp2);

  // x' = alpha^2 - 8*beta
  fiat_p256_square(x_out, alpha);
  fiat_p256_add(fourbeta, beta, beta);
  fiat_p256_add(fourbeta, fourbeta, fourbeta);
  fiat_p256_add(tmptmp, fourbeta, fourbeta);
  fiat_p256_sub(x_out, x_out, tmptmp);

  // z' = (y + z)^2 - gamma - delta
  fiat_p256_add(delta, gamma, delta);
  fiat_p256_add(ftmp, y_in, z_in);
  fiat_p256_square(z_out, ftmp);
  fiat_p256_sub(z_out, z_out, delta);

  // y' = alpha*(4*beta - x') - 8*gamma^2
  fiat_p256_sub(y_out, fourbeta, x_out);
  fiat_p256_add(gamma, gamma, gamma);
  fiat_p256_square(gamma, gamma);
  fiat_p256_mul(y_out, alpha, y_out);
  fiat_p256_add(gamma, gamma, gamma);
  fiat_p256_sub(y_out, y_out, gamma);
}

// fiat_p256_point_add calculates (x1, y1, z1) + (x2, y2, z2)
//
// The method is taken from:
//   http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-3.html#addition-add-2007-bl,
// adapted for mixed addition (z2 = 1, or z2 = 0 for the point at infinity).
//
// Coq transcription and correctness proof:
// <https://github.com/mit-plv/fiat-crypto/blob/79f8b5f39ed609339f0233098dee1a3c4e6b3080/src/Curves/Weierstrass/Jacobian.v#L135>
// <https://github.com/mit-plv/fiat-crypto/blob/79f8b5f39ed609339f0233098dee1a3c4e6b3080/src/Curves/Weierstrass/Jacobian.v#L205>
//
// This function includes a branch for checking whether the two input points
// are equal, (while not equal to the point at infinity). This case never
// happens during single point multiplication, so there is no timing leak for
// ECDH or ECDSA signing.
void fiat_p256_point_add(fiat_p256_felem x3, fiat_p256_felem y3,
                                fiat_p256_felem z3, const fiat_p256_felem x1,
                                const fiat_p256_felem y1,
                                const fiat_p256_felem z1, const int mixed,
                                const fiat_p256_felem x2,
                                const fiat_p256_felem y2,
                                const fiat_p256_felem z2) {
  fiat_p256_felem x_out, y_out, z_out;
  fiat_p256_limb_t z1nz = fiat_p256_nz(z1);
  fiat_p256_limb_t z2nz = fiat_p256_nz(z2);

  // z1z1 = z1z1 = z1**2
  fiat_p256_felem z1z1;
  fiat_p256_square(z1z1, z1);

  fiat_p256_felem u1, s1, two_z1z2;
  if (!mixed) {
    // z2z2 = z2**2
    fiat_p256_felem z2z2;
    fiat_p256_square(z2z2, z2);

    // u1 = x1*z2z2
    fiat_p256_mul(u1, x1, z2z2);

    // two_z1z2 = (z1 + z2)**2 - (z1z1 + z2z2) = 2z1z2
    fiat_p256_add(two_z1z2, z1, z2);
    fiat_p256_square(two_z1z2, two_z1z2);
    fiat_p256_sub(two_z1z2, two_z1z2, z1z1);
    fiat_p256_sub(two_z1z2, two_z1z2, z2z2);

    // s1 = y1 * z2**3
    fiat_p256_mul(s1, z2, z2z2);
    fiat_p256_mul(s1, s1, y1);
  } else {
    // We'll assume z2 = 1 (special case z2 = 0 is handled later).

    // u1 = x1*z2z2
    fiat_p256_copy(u1, x1);
    // two_z1z2 = 2z1z2
    fiat_p256_add(two_z1z2, z1, z1);
    // s1 = y1 * z2**3
    fiat_p256_copy(s1, y1);
  }

  // u2 = x2*z1z1
  fiat_p256_felem u2;
  fiat_p256_mul(u2, x2, z1z1);

  // h = u2 - u1
  fiat_p256_felem h;
  fiat_p256_sub(h, u2, u1);

  fiat_p256_limb_t xneq = fiat_p256_nz(h);

  // z_out = two_z1z2 * h
  fiat_p256_mul(z_out, h, two_z1z2);

  // z1z1z1 = z1 * z1z1
  fiat_p256_felem z1z1z1;
  fiat_p256_mul(z1z1z1, z1, z1z1);

  // s2 = y2 * z1**3
  fiat_p256_felem s2;
  fiat_p256_mul(s2, y2, z1z1z1);

  // r = (s2 - s1)*2
  fiat_p256_felem r;
  fiat_p256_sub(r, s2, s1);
  fiat_p256_add(r, r, r);

  fiat_p256_limb_t yneq = fiat_p256_nz(r);

  fiat_p256_limb_t is_nontrivial_double = constant_time_is_zero_w(xneq | yneq) &
                                          ~constant_time_is_zero_w(z1nz) &
                                          ~constant_time_is_zero_w(z2nz);
  if (is_nontrivial_double) {
    fiat_p256_point_double(x3, y3, z3, x1, y1, z1);
    return;
  }

  // I = (2h)**2
  fiat_p256_felem i;
  fiat_p256_add(i, h, h);
  fiat_p256_square(i, i);

  // J = h * I
  fiat_p256_felem j;
  fiat_p256_mul(j, h, i);

  // V = U1 * I
  fiat_p256_felem v;
  fiat_p256_mul(v, u1, i);

  // x_out = r**2 - J - 2V
  fiat_p256_square(x_out, r);
  fiat_p256_sub(x_out, x_out, j);
  fiat_p256_sub(x_out, x_out, v);
  fiat_p256_sub(x_out, x_out, v);

  // y_out = r(V-x_out) - 2 * s1 * J
  fiat_p256_sub(y_out, v, x_out);
  fiat_p256_mul(y_out, y_out, r);
  fiat_p256_felem s1j;
  fiat_p256_mul(s1j, s1, j);
  fiat_p256_sub(y_out, y_out, s1j);
  fiat_p256_sub(y_out, y_out, s1j);

  fiat_p256_cmovznz(x_out, z1nz, x2, x_out);
  fiat_p256_cmovznz(x3, z2nz, x1, x_out);
  fiat_p256_cmovznz(y_out, z1nz, y2, y_out);
  fiat_p256_cmovznz(y3, z2nz, y1, y_out);
  fiat_p256_cmovznz(z_out, z1nz, z2, z_out);
  fiat_p256_cmovznz(z3, z2nz, z1, z_out);
}

void GFp_nistz256_add(P256_POINT *r, const P256_POINT *a, const P256_POINT *b) {
  fiat_p256_point_add(r->X, r->Y, r->Z,
                      a->X, a->Y, a->Z,
                      0,
                      b->X, b->Y, b->Z);
}

void GFp_nistz256_mul_mont(Limb r[P256_LIMBS], const Limb a[P256_LIMBS],
                       const Limb b[P256_LIMBS]) {
  fiat_p256_mul(r, a, b);
}

/*
void GFp_nistz256_sqr_mont(Limb r[P256_LIMBS], const Limb a[P256_LIMBS]) {
  fiat_p256_square(r, a);
}*/

void GFp_nistz256_point_double(P256_POINT *r, const P256_POINT *a) {
  fiat_p256_point_double(r->X, r->Y, r->Z,
                         a->X, a->Y, a->Z);
}

/* Modular neg: res = -a mod P */
void GFp_nistz256_neg(Limb res[P256_LIMBS], const Limb a[P256_LIMBS]) {
  fiat_p256_opp(res, a);
}
