-- Prove2me | solution 1 for CrossLicensing.Innovation.monopoly_infeasible
-- status  : ACCEPTED   (prove)
-- author  : @Yuhang Yang
-- created : 2026-10-17T10:41:41.626096+00:00
-- url     : https://prove2.me/submissions/891b91d9-bfd4-4df8-bd85-47261801451e

import Definitions.Def_CrossLicensing_Innovation_ClosedForms
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open CrossLicensing.Innovation

theorem solution (β k2 : ℝ) (hk2 : 49 / 144 < k2) (hβ0 : 0 ≤ β)
    (hβ : β < Real.sqrt 3 - 1) :
    0 ≤ 1 / (16 * k2 - 1) ∧
    (∀ T2 : ℝ, 0 ≤ T2 → T2 ≠ 1 / (16 * k2 - 1) →
      (T2 + 1) ^ 2 / 16 - k2 * T2 ^ 2 <
        (1 / (16 * k2 - 1) + 1) ^ 2 / 16 - k2 * (1 / (16 * k2 - 1)) ^ 2) ∧
    1 / (16 * k2 - 1) < That2 β 0 := by
  have hd : 0 < 16 * k2 - 1 := by linarith
  have hd0 : 16 * k2 - 1 ≠ 0 := ne_of_gt hd
  refine ⟨le_of_lt (one_div_pos.mpr hd), ?_, ?_⟩
  · intro T2 _hT hne
    have hcoef : 0 < k2 - 1 / 16 := by linarith
    have hsquare : 0 < (T2 - 1 / (16 * k2 - 1)) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    have hgap :
        ((1 / (16 * k2 - 1) + 1) ^ 2 / 16 - k2 * (1 / (16 * k2 - 1)) ^ 2) -
        ((T2 + 1) ^ 2 / 16 - k2 * T2 ^ 2) =
        (k2 - 1 / 16) * (T2 - 1 / (16 * k2 - 1)) ^ 2 := by
      field_simp
      <;> ring
    have hpos := mul_pos hcoef hsquare
    linarith only [hgap, hpos]
  · have hsmall : 1 / (16 * k2 - 1) < (1 / 3 : ℝ) := by
      apply (div_lt_iff₀ hd).2
      linarith
    have hsqrt0 := Real.sqrt_nonneg (3 : ℝ)
    have hsqrt2 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    have hsqrt : Real.sqrt 3 < (7 / 4 : ℝ) := by nlinarith
    have hden : 0 < Real.sqrt 3 - 1 - β := by linarith
    have hboundary : (1 / 3 : ℝ) < That2 β 0 := by
      unfold That2
      simp only [zero_mul, add_zero]
      apply (lt_div_iff₀ hden).2
      linarith
    exact hsmall.trans hboundary

#print axioms solution
