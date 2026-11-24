-- Prove2me | solution 1 for Formalism.ZRN.e_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:43:10.345301+00:00
-- url     : https://prove2.me/submissions/ecc80144-6f4b-41f6-9bb1-0514321106e3

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism
open Formalism.ZRN
namespace Formalism.ZRN
theorem _root_.solution (n : ℕ) (s : ℂ) (hs : ‖1 - s‖ ≤ (n : ℝ) + 1) :
    ‖e n s‖ ≤ (‖1 - s‖ ^ 2 + ‖1 - s‖) * ((n : ℝ) + 1) ^ (-1 - s.re) := by
  set x : ℝ := (n : ℝ) + 1 with hxdef
  have hx0 : 0 < x := by positivity
  set ℓ := Real.log x with hℓ
  set ℓ' := Real.log (x + 1) with hℓ'
  set L := ℓ' - ℓ with hL
  set a : ℂ := 1 - s with ha
  have c1 : ∀ w : ℂ, ((n : ℂ) + 1) ^ w = exp ((ℓ : ℂ) * w) := by
    intro w
    have h1 : ((n : ℂ) + 1) = ((x : ℝ) : ℂ) := by rw [hxdef]; push_cast; ring
    rw [h1, cpow_def_of_ne_zero (by exact_mod_cast hx0.ne'), ← Complex.ofReal_log hx0.le]
  have c2 : ∀ w : ℂ, ((n : ℂ) + 2) ^ w = exp ((ℓ' : ℂ) * w) := by
    intro w
    have h1 : ((n : ℂ) + 2) = ((x + 1 : ℝ) : ℂ) := by rw [hxdef]; push_cast; ring
    rw [h1, cpow_def_of_ne_zero (by exact_mod_cast (by linarith : (0:ℝ) < x + 1).ne'),
      ← Complex.ofReal_log (by linarith)]
  have hE1 : exp ((ℓ : ℂ) * -s) = exp ((ℓ : ℂ) * a) * ((x : ℂ))⁻¹ := by
    have : (ℓ : ℂ) * -s = (ℓ : ℂ) * a + -(ℓ : ℂ) := by rw [ha]; ring
    rw [this, Complex.exp_add, Complex.exp_neg, ← Complex.ofReal_exp, hℓ, Real.exp_log hx0]
  have hE2 : exp ((ℓ' : ℂ) * a) = exp ((ℓ : ℂ) * a) * exp (a * (L : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; rw [hL]; push_cast; ring
  have key : e n s = exp ((ℓ : ℂ) * a) *
      (-(exp (a * (L : ℂ)) - 1 - a * (L : ℂ)) + a * (((x : ℂ))⁻¹ - (L : ℂ))) := by
    unfold e
    rw [← ha, c1, c1, c2, hE1, hE2]
    ring
  have hLle : L ≤ x⁻¹ := by
    have := Real.log_le_sub_one_of_pos (x := (x + 1) / x) (by positivity)
    rw [Real.log_div (by linarith) hx0.ne'] at this
    rw [hL, hℓ, hℓ']
    calc _ ≤ (x + 1) / x - 1 := this
      _ = x⁻¹ := by field_simp; ring
  have hLge : (x + 1)⁻¹ ≤ L := by
    have := Real.one_sub_inv_le_log_of_pos (x := (x + 1) / x) (by positivity)
    rw [Real.log_div (by linarith) hx0.ne'] at this
    rw [hL, hℓ, hℓ']
    calc (x + 1)⁻¹ = 1 - ((x + 1) / x)⁻¹ := by field_simp; ring
      _ ≤ _ := this
  have hL0 : 0 ≤ L := le_trans (by positivity) hLge
  have hd : x⁻¹ - L ≤ (x ^ 2)⁻¹ := by
    have h3 : x⁻¹ - (x + 1)⁻¹ = (x * (x + 1))⁻¹ := by field_simp; ring
    have h4 : (x * (x + 1))⁻¹ ≤ (x ^ 2)⁻¹ := inv_anti₀ (by positivity) (by nlinarith)
    linarith
  have hna : 0 ≤ ‖a‖ := norm_nonneg _
  have hnX : ‖exp ((ℓ : ℂ) * a)‖ = Real.exp (ℓ * (1 - s.re)) := by
    rw [Complex.norm_exp]; congr 1; rw [ha]; simp
  have hnaL : ‖a * (L : ℂ)‖ = ‖a‖ * L := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL0]
  have hz : ‖a * (L : ℂ)‖ ≤ 1 := by
    rw [hnaL]
    calc ‖a‖ * L ≤ x * x⁻¹ := mul_le_mul hs hLle hL0 hx0.le
      _ = 1 := mul_inv_cancel₀ hx0.ne'
  have hexp := Complex.norm_exp_sub_one_sub_id_le hz
  have hsq : ‖a * (L : ℂ)‖ ^ 2 ≤ ‖a‖ ^ 2 * (x ^ 2)⁻¹ := by
    rw [hnaL, mul_pow, ← inv_pow]
    gcongr
  have hlin : ‖a * (((x : ℂ))⁻¹ - (L : ℂ))‖ ≤ ‖a‖ * (x ^ 2)⁻¹ := by
    have : ((x : ℂ))⁻¹ - (L : ℂ) = ((x⁻¹ - L : ℝ) : ℂ) := by push_cast; ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_left hd hna
  have hx2 : x ^ 2 = Real.exp (2 * ℓ) := by
    rw [show 2 * ℓ = ℓ + ℓ by ring, Real.exp_add, hℓ, Real.exp_log hx0]; ring
  rw [key, norm_mul, hnX]
  calc Real.exp (ℓ * (1 - s.re)) *
        ‖-(exp (a * (L : ℂ)) - 1 - a * (L : ℂ)) + a * (((x : ℂ))⁻¹ - (L : ℂ))‖
      ≤ Real.exp (ℓ * (1 - s.re)) * (‖a‖ ^ 2 * (x ^ 2)⁻¹ + ‖a‖ * (x ^ 2)⁻¹) := by
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
        linarith
    _ = (‖a‖ ^ 2 + ‖a‖) * (Real.exp (ℓ * (1 - s.re)) * (x ^ 2)⁻¹) := by ring
    _ = (‖a‖ ^ 2 + ‖a‖) * x ^ (-1 - s.re) := by
        congr 1
        rw [Real.rpow_def_of_pos hx0, hx2, ← Real.exp_neg, ← Real.exp_add]
        congr 1
        ring
end Formalism.ZRN
