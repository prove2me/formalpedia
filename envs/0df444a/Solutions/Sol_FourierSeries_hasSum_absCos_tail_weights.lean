-- Prove2me | solution 1 for FourierSeries.hasSum_absCos_tail_weights
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:26:21.183217+00:00
-- url     : https://prove2.me/submissions/7214a832-ed35-4375-a518-5166844b9473

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.MR.AbsCosFourier =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey
-/

/-!
# A4F H1 — the exact-series majorization of `|cos|`

The classical Fourier expansion, with its truncation error EXACT at every cutoff:

`|cos θ| = 2/π + (4/π) Σ_{m≥1} (−1)^{m+1} cos(2mθ)/(4m²−1)`,

and for every cutoff `Mcut` the two-sided bound

`| |cos θ| − 2/π − (4/π) Σ_{m=1}^{Mcut} (−1)^{m+1} cos(2mθ)/(4m²−1) | ≤ 2/(π(2Mcut+1))`.

This is the harmonic control the A4F mid-range wave consumes: it converts the sifted sum
`Σ_p (1 − |cos(u·log p/2)|)/p` into a Mertens main term at weight `1 − 2/π` plus finitely
many harmonic sums `Σ_p cos(mu·log p)/p`, each carrying weight `(4/π)/(4m²−1)` — the head
weights sum to `(4/π)·Mcut/(2Mcut+1) < 2/π` (exact partial sum below), bounded independent
of the cutoff, and the tail is `2/(π(2Mcut+1))`, which at `Mcut ≈ loglog X` is absorbable.

**TWO-SIDED BY NECESSITY.**  The series carries BOTH signs (`(−1)^{m+1}`), so the harmonic
sums must be controlled two-sidedly; a one-sided majorant cannot substitute.  The
commissioning fold's refuter pass priced the cheap alternative out: a single-harmonic
majorant `|cos θ| ≤ a₀ + a₁·cos(2θ)` forces `a₀ ≥ |cos(π/4)| = 1/√2` by evaluation at
`θ = π/4` (where the harmonic vanishes) — kernel-checked below as
`one_sided_majorant_head_floor` — and the excess `1/√2 − 2/π ≈ 0.0705` already exceeds the
`3/50 = 0.06` bar the far-branch constant chain must clear.  The exact series loses NOTHING
at the head, which is why the route closes at the sharp constant.

Proof route: `|cos|` is `π`-periodic, so it lifts to `C(AddCircle π, ℂ)`; its Fourier
coefficients are computed exactly (both exponents `1 ± 2n` are odd, so no degenerate case
arises in the exponential integrals); they are summable, so mathlib's
`has_pointwise_sum_fourier_series_of_summable` gives the identity pointwise; pairing `n`
with `−n` produces the real cosine series, and the tail telescopes exactly.
-/

namespace Salt.MR

open Complex (I)
open intervalIntegral

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

/-! ## The circle lift of `|cos|` -/

/-- `|cos|` is `π`-periodic (as a ℂ-valued function, for the Fourier machinery). -/
lemma absCos_ofReal_periodic :
    Function.Periodic (fun x : ℝ => ((|Real.cos x| : ℝ) : ℂ)) Real.pi := by
  intro x
  have h : Real.cos (x + Real.pi) = -Real.cos x := by
    rw [Real.cos_add, Real.cos_pi, Real.sin_pi]; ring
  simp [h, abs_neg]

/-- The lift of `|cos|` to the circle of circumference `π`. -/
noncomputable def absCosCircle : C(AddCircle Real.pi, ℂ) where
  toFun := absCos_ofReal_periodic.lift
  continuous_toFun := by
    rw [(QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples Real.pi)).continuous_iff]
    exact Complex.continuous_ofReal.comp (_root_.continuous_abs.comp Real.continuous_cos)

@[simp] lemma absCosCircle_coe (θ : ℝ) :
    absCosCircle (θ : AddCircle Real.pi) = ((|Real.cos θ| : ℝ) : ℂ) := rfl

/-! ## Powers of `I` at odd integer exponents -/

lemma neg_one_zpow_inv (n : ℤ) : ((-1 : ℂ) ^ n)⁻¹ = (-1 : ℂ) ^ n := by
  refine inv_eq_of_mul_eq_one_left ?_
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), show n + n = 2 * n by ring, zpow_mul,
    show ((-1 : ℂ)) ^ (2 : ℤ) = 1 by norm_num, one_zpow]

lemma I_zpow_two_mul (n : ℤ) : (I : ℂ) ^ (2 * n) = (-1 : ℂ) ^ n := by
  rw [zpow_mul, show (I : ℂ) ^ (2 : ℤ) = -1 by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, Complex.I_sq]]

lemma I_zpow_one_add_two_mul (n : ℤ) : (I : ℂ) ^ (1 + 2 * n) = (-1 : ℂ) ^ n * I := by
  rw [zpow_add₀ Complex.I_ne_zero, zpow_one, I_zpow_two_mul, mul_comm]

lemma I_zpow_one_sub_two_mul (n : ℤ) : (I : ℂ) ^ (1 - 2 * n) = (-1 : ℂ) ^ n * I := by
  rw [show (1 - 2 * n) = 1 + 2 * (-n) by ring, I_zpow_one_add_two_mul, zpow_neg,
    neg_one_zpow_inv]

/-- `exp(k · (π/2)·I) = I^k` for every integer `k`. -/
lemma exp_int_mul_half_pi_I (k : ℤ) :
    Complex.exp ((k : ℂ) * ((Real.pi : ℂ) / 2 * I)) = I ^ k := by
  rw [Complex.exp_int_mul]
  congr 1
  rw [Complex.exp_mul_I]
  have hc : Complex.cos ((Real.pi : ℂ) / 2) = 0 := by
    rw [show ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]
  have hs : Complex.sin ((Real.pi : ℂ) / 2) = 1 := by
    rw [show ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_sin, Real.sin_pi_div_two, Complex.ofReal_one]
  rw [hc, hs, one_mul, zero_add]

/-! ## The Fourier coefficients of `|cos|`, exact -/

/-- The `n`-th Fourier coefficient of `|cos|` on the circle of circumference `π` is
`(2/π)·(−1)^{n+1}/(4n²−1)`.  Both exponentials in the expansion of `cos` carry the odd
exponents `1 ± 2n`, so the exponential integrals never degenerate. -/
theorem fourierCoeff_absCosCircle (n : ℤ) :
    fourierCoeff (⇑absCosCircle) n
      = (((2 / Real.pi * ((-1 : ℝ) ^ (n + 1) / (4 * (n : ℝ) ^ 2 - 1))) : ℝ) : ℂ) := by
  have hπC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1Z : (1 - 2 * n : ℤ) ≠ 0 := by omega
  have h2Z : (1 + 2 * n : ℤ) ≠ 0 := by omega
  have h1C : ((1 : ℂ) - 2 * n) ≠ 0 := by
    have := Int.cast_ne_zero (α := ℂ) |>.mpr h1Z; push_cast at this; exact this
  have h2C : ((1 : ℂ) + 2 * n) ≠ 0 := by
    have := Int.cast_ne_zero (α := ℂ) |>.mpr h2Z; push_cast at this; exact this
  have hle : -(Real.pi / 2) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  -- the coefficient as an interval integral on [−π/2, π/2]
  rw [fourierCoeff_eq_intervalIntegral (⇑absCosCircle) n (-(Real.pi / 2)),
    show -(Real.pi / 2) + Real.pi = Real.pi / 2 by ring]
  -- rewrite the integrand as a sum of two exponentials with odd frequencies
  have hInt : (∫ x in (-(Real.pi / 2))..(Real.pi / 2),
        fourier (-n) (x : AddCircle Real.pi) • absCosCircle (x : AddCircle Real.pi))
      = ∫ x in (-(Real.pi / 2))..(Real.pi / 2),
          (Complex.exp ((((1 : ℂ) - 2 * n) * I) * x)
            + Complex.exp ((-((1 : ℂ) + 2 * n) * I) * x)) / 2 := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hle] at hx
    have hcosx : |Real.cos x| = Real.cos x :=
      abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1], hx.2⟩)
    rw [absCosCircle_coe, fourier_coe_apply, hcosx, Complex.ofReal_cos]
    have hfreq : 2 * (Real.pi : ℂ) * I * (-n : ℤ) * x / Real.pi = (-(2 * n) * I) * x := by
      push_cast
      rw [div_eq_iff hπC]
      ring
    rw [hfreq]
    have hcos : Complex.cos (x : ℂ)
        = (Complex.exp ((x : ℂ) * I) + Complex.exp (-(x : ℂ) * I)) / 2 := by
      have := Complex.two_cos (x : ℂ)
      linear_combination this / 2
    rw [smul_eq_mul, hcos, ← mul_div_assoc, mul_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 3 <;> ring
  rw [hInt]
  -- integrate the two exponentials
  have hcont : ∀ c : ℂ, IntervalIntegrable (fun x : ℝ => Complex.exp (c * x))
      MeasureTheory.volume (-(Real.pi / 2)) (Real.pi / 2) := fun c =>
    (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hcont _) (hcont _),
    integral_exp_mul_complex (by simpa using mul_ne_zero h1C Complex.I_ne_zero),
    integral_exp_mul_complex (by simpa using mul_ne_zero (neg_ne_zero.mpr h2C) Complex.I_ne_zero)]
  -- evaluate the four endpoint exponentials as powers of I
  have e1b : ((1 : ℂ) - 2 * n) * I * (Real.pi / 2 : ℝ)
      = ((1 - 2 * n : ℤ) : ℂ) * ((Real.pi : ℂ) / 2 * I) := by push_cast; ring
  have e1a : ((1 : ℂ) - 2 * n) * I * (-(Real.pi / 2) : ℝ)
      = ((-(1 - 2 * n) : ℤ) : ℂ) * ((Real.pi : ℂ) / 2 * I) := by push_cast; ring
  have e2b : -((1 : ℂ) + 2 * n) * I * (Real.pi / 2 : ℝ)
      = ((-(1 + 2 * n) : ℤ) : ℂ) * ((Real.pi : ℂ) / 2 * I) := by push_cast; ring
  have e2a : -((1 : ℂ) + 2 * n) * I * (-(Real.pi / 2) : ℝ)
      = (((1 + 2 * n) : ℤ) : ℂ) * ((Real.pi : ℂ) / 2 * I) := by push_cast; ring
  rw [e1b, e1a, e2b, e2a, exp_int_mul_half_pi_I, exp_int_mul_half_pi_I,
    exp_int_mul_half_pi_I, exp_int_mul_half_pi_I]
  have p1 : (I : ℂ) ^ (1 - 2 * n : ℤ) = (-1 : ℂ) ^ n * I := I_zpow_one_sub_two_mul n
  have p1' : (I : ℂ) ^ (-(1 - 2 * n) : ℤ) = ((-1 : ℂ) ^ n * I)⁻¹ := by
    rw [zpow_neg, p1]
  have p2 : (I : ℂ) ^ (1 + 2 * n : ℤ) = (-1 : ℂ) ^ n * I := I_zpow_one_add_two_mul n
  have p2' : (I : ℂ) ^ (-(1 + 2 * n) : ℤ) = ((-1 : ℂ) ^ n * I)⁻¹ := by
    rw [zpow_neg, p2]
  rw [p1, p1', p2, p2']
  -- close by field arithmetic; the smul is a real scalar
  have hinv : ((-1 : ℂ) ^ n * I)⁻¹ = (-1 : ℂ) ^ n * (-I) := by
    rw [mul_inv, neg_one_zpow_inv, Complex.inv_I]
  have hzpow1 : (-1 : ℂ) ^ (n + 1) = -((-1 : ℂ) ^ n) := by
    rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]; ring
  have hcast : (((2 / Real.pi * ((-1 : ℝ) ^ (n + 1) / (4 * (n : ℝ) ^ 2 - 1))) : ℝ) : ℂ)
      = 2 / (Real.pi : ℂ) * ((-1 : ℂ) ^ (n + 1) / (4 * (n : ℂ) ^ 2 - 1)) := by
    push_cast [Complex.ofReal_zpow]
    norm_num
  have h4C : (4 * (n : ℂ) ^ 2 - 1) ≠ 0 := by
    have := mul_ne_zero h1C h2C
    intro hcon
    apply this
    linear_combination -hcon
  rw [hinv, hcast, hzpow1, Complex.real_smul]
  have hs : (-1 : ℂ) ^ n ≠ 0 := zpow_ne_zero _ (by norm_num)
  have h4C' : (-1 + (n : ℂ) ^ 2 * 4) ≠ 0 := fun hcon => h4C (by linear_combination hcon)
  push_cast
  field_simp [h1C, h2C, h4C, h4C', hs]
  linear_combination (-4 : ℂ) * mul_inv_cancel₀ h4C'

/-! ## Summability of the coefficients -/

theorem summable_fourierCoeff_absCosCircle :
    Summable (fun n : ℤ => fourierCoeff (⇑absCosCircle) n) := by
  refine Summable.of_norm ?_
  have hval : ∀ n : ℤ, ‖fourierCoeff (⇑absCosCircle) n‖
      = 2 / Real.pi * (1 / |4 * (n : ℝ) ^ 2 - 1|) := by
    intro n
    rw [fourierCoeff_absCosCircle, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.pi), abs_div, abs_zpow]
    norm_num
  have hnat : Summable (fun m : ℕ => 1 / |4 * (m : ℝ) ^ 2 - 1|) := by
    rw [← summable_nat_add_iff 1]
    have hb : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
      have h0 := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      have h1 := (summable_nat_add_iff 1).mpr h0
      refine h1.congr fun m => ?_
      push_cast
      ring
    refine hb.of_nonneg_of_le (fun m => by positivity) fun m => ?_
    have h1 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have habs : |4 * (((m + 1 : ℕ)) : ℝ) ^ 2 - 1| = 4 * ((m : ℝ) + 1) ^ 2 - 1 := by
      rw [abs_of_pos (by push_cast; nlinarith)]
      push_cast
      ring
    rw [habs]
    have hle : ((m : ℝ) + 1) ^ 2 ≤ 4 * ((m : ℝ) + 1) ^ 2 - 1 := by nlinarith
    exact one_div_le_one_div_of_le (by positivity) hle
  have hZ : Summable (fun n : ℤ => 1 / |4 * (n : ℝ) ^ 2 - 1|) := by
    have hposS : Summable (fun m : ℕ => 1 / |4 * ((m : ℤ) : ℝ) ^ 2 - 1|) := by
      refine hnat.congr fun m => ?_
      norm_num
    have hnegS : Summable (fun m : ℕ => 1 / |4 * (((-m : ℤ)) : ℝ) ^ 2 - 1|) := by
      refine hnat.congr fun m => ?_
      rw [show (((-m : ℤ)) : ℝ) ^ 2 = ((m : ℝ)) ^ 2 by push_cast; ring]
    exact hposS.of_nat_of_neg hnegS
  refine (hZ.mul_left (2 / Real.pi)).congr fun n => (hval n).symm

/-! ## The pointwise identity, paired into real harmonics -/

lemma neg_one_zpow_real_neg_add_one (m : ℤ) : (-1 : ℝ) ^ (-m + 1) = (-1 : ℝ) ^ (m + 1) := by
  rw [show -m + 1 = (m + 1) + 2 * (-m) by ring, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0),
    zpow_mul, show ((-1 : ℝ)) ^ (2 : ℤ) = 1 by norm_num, one_zpow, mul_one]

/-- The Fourier series of `|cos|`, paired into real harmonics: for every `θ`,
`Σ_{m≥0} (4/π)·(−1)^m·cos(2(m+1)θ)/(4(m+1)²−1) = |cos θ| − 2/π`.  (The harmonic of index
`m` here is the `(m+1)`-st cosine; the alternating sign `(−1)^m` is `(−1)^{(m+1)+1}`.) -/
theorem hasSum_absCos_harmonics (θ : ℝ) :
    HasSum (fun m : ℕ => 4 / Real.pi
        * ((-1 : ℝ) ^ m * Real.cos (2 * ((m : ℝ) + 1) * θ) / (4 * ((m : ℝ) + 1) ^ 2 - 1)))
      (|Real.cos θ| - 2 / Real.pi) := by
  have hπC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h0 := has_pointwise_sum_fourier_series_of_summable
    (f := absCosCircle) summable_fourierCoeff_absCosCircle (θ : AddCircle Real.pi)
  have h1 := h0.nat_add_neg
  rw [absCosCircle_coe] at h1
  -- each paired term is real
  have hterm : ∀ m : ℕ,
      fourierCoeff (⇑absCosCircle) (m : ℤ) • fourier (m : ℤ) (θ : AddCircle Real.pi)
        + fourierCoeff (⇑absCosCircle) (-(m : ℤ)) • fourier (-(m : ℤ)) (θ : AddCircle Real.pi)
      = (((2 / Real.pi * ((-1 : ℝ) ^ ((m : ℤ) + 1) / (4 * (((m : ℤ)) : ℝ) ^ 2 - 1)))
          * (2 * Real.cos (2 * (m : ℝ) * θ)) : ℝ) : ℂ) := by
    intro m
    rw [fourierCoeff_absCosCircle, fourierCoeff_absCosCircle, fourier_coe_apply,
      fourier_coe_apply]
    simp only [Int.cast_neg, neg_sq]
    rw [neg_one_zpow_real_neg_add_one]
    have hfm : 2 * (Real.pi : ℂ) * I * (((m : ℤ)) : ℂ) * (θ : ℂ) / (Real.pi : ℂ)
        = ((2 * (m : ℝ) * θ : ℝ) : ℂ) * I := by
      push_cast
      rw [div_eq_iff hπC]
      ring
    have hfm' : 2 * (Real.pi : ℂ) * I * -(((m : ℤ)) : ℂ) * (θ : ℂ) / (Real.pi : ℂ)
        = -((2 * (m : ℝ) * θ : ℝ) : ℂ) * I := by
      push_cast
      rw [div_eq_iff hπC]
      ring
    rw [hfm, hfm', smul_eq_mul, smul_eq_mul, ← mul_add, ← Complex.two_cos,
      ← Complex.ofReal_cos]
    push_cast
    ring
  have hfun : (fun m : ℕ =>
      fourierCoeff (⇑absCosCircle) (m : ℤ) • fourier (m : ℤ) (θ : AddCircle Real.pi)
        + fourierCoeff (⇑absCosCircle) (-(m : ℤ)) • fourier (-(m : ℤ)) (θ : AddCircle Real.pi))
      = fun m : ℕ => (((2 / Real.pi * ((-1 : ℝ) ^ ((m : ℤ) + 1)
          / (4 * (((m : ℤ)) : ℝ) ^ 2 - 1)))
          * (2 * Real.cos (2 * (m : ℝ) * θ)) : ℝ) : ℂ) := funext hterm
  rw [hfun] at h1
  -- the `n = 0` term of the ℤ-sum
  have hg0 : fourierCoeff (⇑absCosCircle) (0 : ℤ) • fourier (0 : ℤ) (θ : AddCircle Real.pi)
      = (((2 / Real.pi : ℝ)) : ℂ) := by
    rw [fourierCoeff_absCosCircle, fourier_zero, smul_eq_mul, mul_one]
    norm_num
  rw [hg0, ← Complex.ofReal_add] at h1
  -- drop to ℝ
  have h2 := Complex.hasSum_ofReal.mp h1
  -- peel the `m = 0` pair
  have h4 := (hasSum_nat_add_iff' (f := fun m : ℕ => 2 / Real.pi
      * ((-1 : ℝ) ^ ((m : ℤ) + 1) / (4 * (((m : ℤ)) : ℝ) ^ 2 - 1))
      * (2 * Real.cos (2 * (m : ℝ) * θ))) 1).mpr h2
  rw [Finset.sum_range_one] at h4
  have hval0 : (|Real.cos θ| + 2 / Real.pi) - 2 / Real.pi
      * ((-1 : ℝ) ^ (((0 : ℕ) : ℤ) + 1) / (4 * ((((0 : ℕ) : ℤ)) : ℝ) ^ 2 - 1))
      * (2 * Real.cos (2 * ((0 : ℕ) : ℝ) * θ)) = |Real.cos θ| - 2 / Real.pi := by
    norm_num
    ring
  rw [hval0] at h4
  have hfin : (fun n : ℕ => 2 / Real.pi
      * ((-1 : ℝ) ^ (((n + 1 : ℕ) : ℤ) + 1) / (4 * ((((n + 1 : ℕ) : ℤ)) : ℝ) ^ 2 - 1))
      * (2 * Real.cos (2 * ((n + 1 : ℕ) : ℝ) * θ)))
      = fun m : ℕ => 4 / Real.pi
        * ((-1 : ℝ) ^ m * Real.cos (2 * ((m : ℝ) + 1) * θ) / (4 * ((m : ℝ) + 1) ^ 2 - 1)) := by
    funext m
    have hz : ((-1 : ℝ)) ^ (((m + 1 : ℕ) : ℤ) + 1) = (-1 : ℝ) ^ m := by
      rw [show ((m + 1 : ℕ) : ℤ) + 1 = ((m + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
        pow_succ, pow_succ]
      ring
    rw [hz, show Real.cos (2 * ((m + 1 : ℕ) : ℝ) * θ) = Real.cos (2 * ((m : ℝ) + 1) * θ) by
      congr 1; push_cast; ring]
    push_cast
    ring
  rw [hfin] at h4
  exact h4

/-! ## The tail telescopes exactly -/

/-- `Σ_{k≥0} 1/(4(Mcut+k+1)²−1) = 1/(2(2·Mcut+1))` — the truncation tail, exact.

The cutoff binder is `Mcut`, matching `absCos_weight_partial_sum` and
`abs_cos_partial_fourier_bound` below; the bare `M` this lemma carried until
2026-09-01 was the one spelling in the file that did not (PR #5/#6 review
finding, DESK row AX). Statement and proof are otherwise byte-identical — a
binder rename, nothing more. -/
lemma hasSum_absCos_tail_weights (Mcut : ℕ) :
    HasSum (fun k : ℕ => 1 / (4 * ((Mcut : ℝ) + (k : ℝ) + 1) ^ 2 - 1))
      (1 / (2 * (2 * (Mcut : ℝ) + 1))) := by
  set b : ℕ → ℝ := fun k => (1 / 2) / (2 * ((Mcut : ℝ) + (k : ℝ)) + 1) with hb
  have hposd : ∀ k : ℕ, (0 : ℝ) < 2 * ((Mcut : ℝ) + (k : ℝ)) + 1 := fun k => by positivity
  have hterm : ∀ k : ℕ, 1 / (4 * ((Mcut : ℝ) + (k : ℝ) + 1) ^ 2 - 1) = b k - b (k + 1) := by
    intro k
    have h1 := hposd k
    have h2 := hposd (k + 1)
    push_cast at h2
    simp only [hb]
    push_cast
    rw [div_sub_div _ _ (by linarith) (by linarith),
      show 4 * ((Mcut : ℝ) + (k : ℝ) + 1) ^ 2 - 1
        = (2 * ((Mcut : ℝ) + (k : ℝ)) + 1) * (2 * ((Mcut : ℝ) + ((k : ℝ) + 1)) + 1) by ring,
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hnn : ∀ k : ℕ, (0 : ℝ) ≤ 1 / (4 * ((Mcut : ℝ) + (k : ℝ) + 1) ^ 2 - 1) := by
    intro k
    have h1 : (1 : ℝ) ≤ (Mcut : ℝ) + (k : ℝ) + 1 := by
      have hMcut := Nat.cast_nonneg (α := ℝ) Mcut
      have hk := Nat.cast_nonneg (α := ℝ) k
      linarith
    have : (0 : ℝ) < 4 * ((Mcut : ℝ) + (k : ℝ) + 1) ^ 2 - 1 := by nlinarith
    positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hpart : ∀ n : ℕ,
      ∑ k ∈ Finset.range n, (1 / (4 * ((Mcut : ℝ) + (k : ℝ) + 1) ^ 2 - 1)) = b 0 - b n := by
    intro n
    rw [Finset.sum_congr rfl fun k _ => hterm k]
    exact Finset.sum_range_sub' b n
  simp only [hpart]
  have hb0 : b 0 = 1 / (2 * (2 * (Mcut : ℝ) + 1)) := by
    simp only [hb, Nat.cast_zero, add_zero]
    rw [div_div]
  have hbtend : Filter.Tendsto b Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.div_atTop (tendsto_const_nhds (x := (1 / 2 : ℝ)))
    apply Filter.tendsto_atTop_add_const_right
    apply Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    exact Filter.tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hfinal := hbtend.const_sub (b 0)
  rw [sub_zero] at hfinal
  simpa only [hb0] using hfinal

/-! ## The head weights, exact partial sum -/

/-- `Σ_{m=1}^{Mcut} 1/(4m²−1) = Mcut/(2Mcut+1)` — the head weight budget is `< 1/2`,
uniformly in the cutoff; with the `4/π` prefactor the head spends `< 2/π`. -/
lemma absCos_weight_partial_sum (Mcut : ℕ) :
    ∑ m ∈ Finset.Icc 1 Mcut, (1 : ℝ) / (4 * (m : ℝ) ^ 2 - 1)
      = (Mcut : ℝ) / (2 * (Mcut : ℝ) + 1) := by
  induction Mcut with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
    have h1 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < 2 * ((n : ℝ) + 1) + 1 := by positivity
    push_cast
    rw [show 4 * ((n : ℝ) + 1) ^ 2 - 1 = (2 * (n : ℝ) + 1) * (2 * ((n : ℝ) + 1) + 1) by ring]
    field_simp
    ring

/-! ## The deliverable: the two-sided truncation bound, tail EXACT -/

/-- **H1.** For every `θ` and every cutoff `Mcut`,
`| |cos θ| − 2/π − (4/π) Σ_{m=1}^{Mcut} (−1)^{m+1} cos(2mθ)/(4m²−1) | ≤ 2/(π(2Mcut+1))`.
The bound is the EXACT tail of the absolutely convergent Fourier series — no smoothing
loss, which is what lets the far-branch chain close at the sharp constant `1 − 2/π`. -/
theorem abs_cos_partial_fourier_bound (θ : ℝ) (Mcut : ℕ) :
    |(|Real.cos θ| - 2 / Real.pi
        - 4 / Real.pi * ∑ m ∈ Finset.Icc 1 Mcut,
            (-1 : ℝ) ^ (m + 1) * Real.cos (2 * (m : ℝ) * θ) / (4 * (m : ℝ) ^ 2 - 1))|
      ≤ 2 / (Real.pi * (2 * (Mcut : ℝ) + 1)) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hS := hasSum_absCos_harmonics θ
  set t : ℕ → ℝ := fun m => 4 / Real.pi
      * ((-1 : ℝ) ^ m * Real.cos (2 * ((m : ℝ) + 1) * θ) / (4 * ((m : ℝ) + 1) ^ 2 - 1))
    with ht
  -- the head partial sum, reindexed `range Mcut → Icc 1 Mcut`
  have hhead : ∑ k ∈ Finset.range Mcut, t k
      = 4 / Real.pi * ∑ m ∈ Finset.Icc 1 Mcut,
          (-1 : ℝ) ^ (m + 1) * Real.cos (2 * (m : ℝ) * θ) / (4 * (m : ℝ) ^ 2 - 1) := by
    induction Mcut with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), mul_add]
      congr 1
      simp only [ht]
      rw [show Real.cos (2 * (((n + 1 : ℕ)) : ℝ) * θ) = Real.cos (2 * ((n : ℝ) + 1) * θ) by
        congr 1; push_cast; ring]
      push_cast
      ring
  -- the tail as a `HasSum`
  have htail := (hasSum_nat_add_iff' (f := t) Mcut).mpr hS
  -- the comparison weights
  have hw := (hasSum_absCos_tail_weights Mcut).mul_left (4 / Real.pi)
  have hcmp : ∀ k : ℕ,
      |t (k + Mcut)| ≤ 4 / Real.pi * (1 / (4 * ((Mcut : ℝ) + (k : ℝ) + 1) ^ 2 - 1)) := by
    intro k
    have h1 : (1 : ℝ) ≤ (Mcut : ℝ) + (k : ℝ) + 1 := by
      have hMcut := Nat.cast_nonneg (α := ℝ) Mcut
      have hk := Nat.cast_nonneg (α := ℝ) k
      linarith
    have hpos : (0 : ℝ) < 4 * ((Mcut : ℝ) + (k : ℝ) + 1) ^ 2 - 1 := by nlinarith
    have hval : t (k + Mcut) = 4 / Real.pi
        * ((-1 : ℝ) ^ (k + Mcut) * Real.cos (2 * ((Mcut : ℝ) + (k : ℝ) + 1) * θ)
            / (4 * ((Mcut : ℝ) + (k : ℝ) + 1) ^ 2 - 1)) := by
      simp only [ht]
      rw [show Real.cos (2 * (((k + Mcut : ℕ) : ℝ) + 1) * θ)
          = Real.cos (2 * ((Mcut : ℝ) + (k : ℝ) + 1) * θ) by congr 1; push_cast; ring]
      push_cast
      ring
    rw [hval, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 / Real.pi), abs_div,
      abs_of_pos hpos, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hnum : |Real.cos (2 * ((Mcut : ℝ) + (k : ℝ) + 1) * θ)| ≤ 1 := Real.abs_cos_le_one _
    have hstep : |Real.cos (2 * ((Mcut : ℝ) + (k : ℝ) + 1) * θ)|
          / (4 * ((Mcut : ℝ) + (k : ℝ) + 1) ^ 2 - 1)
        ≤ 1 / (4 * ((Mcut : ℝ) + (k : ℝ) + 1) ^ 2 - 1) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hpos.le)
    exact mul_le_mul_of_nonneg_left hstep (by positivity : (0 : ℝ) ≤ 4 / Real.pi)
  -- two-sided squeeze via `hasSum_le`
  have hub : ((|Real.cos θ| - 2 / Real.pi) - ∑ i ∈ Finset.range Mcut, t i)
      ≤ 4 / Real.pi * (1 / (2 * (2 * (Mcut : ℝ) + 1))) :=
    hasSum_le (fun k => (abs_le.mp (hcmp k)).2) htail hw
  have hlb : -(4 / Real.pi * (1 / (2 * (2 * (Mcut : ℝ) + 1))))
      ≤ ((|Real.cos θ| - 2 / Real.pi) - ∑ i ∈ Finset.range Mcut, t i) := by
    refine hasSum_le (fun k => ?_) hw.neg htail
    exact (abs_le.mp (hcmp k)).1
  have hd : (2 * (Mcut : ℝ) + 1) ≠ 0 := by positivity
  have hBeq : 4 / Real.pi * (1 / (2 * (2 * (Mcut : ℝ) + 1)))
      = 2 / (Real.pi * (2 * (Mcut : ℝ) + 1)) := by
    field_simp
    ring
  rw [show |Real.cos θ| - 2 / Real.pi
        - 4 / Real.pi * ∑ m ∈ Finset.Icc 1 Mcut,
            (-1 : ℝ) ^ (m + 1) * Real.cos (2 * (m : ℝ) * θ) / (4 * (m : ℝ) ^ 2 - 1)
      = (|Real.cos θ| - 2 / Real.pi) - ∑ i ∈ Finset.range Mcut, t i by rw [hhead]]
  rw [← hBeq]
  exact abs_le.mpr ⟨hlb, hub⟩

/-! ## Why one-sided is priced out -/

/-- A single-harmonic ONE-SIDED majorant of `|cos|` pays head constant at least
`1/√2 = √2/2`: evaluate at `θ = π/4`, where the harmonic vanishes.  The excess over the
exact head `2/π` is `≈ 0.0705 > 3/50`, which exceeds the bar the far-branch constant chain
must clear — this is the commissioning fold's pricing of the one-sided route, in the
kernel.  The exact series (above) is two-sided and loses nothing at the head. -/
theorem one_sided_majorant_head_floor (a₀ a₁ : ℝ)
    (h : ∀ θ : ℝ, |Real.cos θ| ≤ a₀ + a₁ * Real.cos (2 * θ)) :
    Real.sqrt 2 / 2 ≤ a₀ := by
  have h4 := h (Real.pi / 4)
  rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two, mul_zero, add_zero,
    Real.cos_pi_div_four] at h4
  calc Real.sqrt 2 / 2 = |Real.sqrt 2 / 2| := (abs_of_nonneg (by positivity)).symm
    _ ≤ a₀ := h4

end Salt.MR

end




section
open Complex (I)

theorem solution (Mcut : ℕ) :
    HasSum (fun k : ℕ => 1 / (4 * ((Mcut : ℝ) + (k : ℝ) + 1) ^ 2 - 1))
      (1 / (2 * (2 * (Mcut : ℝ) + 1))) := by
  apply Salt.MR.hasSum_absCos_tail_weights <;> assumption

end

