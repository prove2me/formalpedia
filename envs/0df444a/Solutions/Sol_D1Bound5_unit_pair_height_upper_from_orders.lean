-- Prove2me | solution 1 for D1Bound5.unit_pair_height_upper_from_orders
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:55:19.11783+00:00
-- url     : https://prove2.me/submissions/10132e6a-9a6a-45be-b785-86a627f2f27a

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions
import Theorems.Thm_D1Bound5_ordinaryLog10_ge_four
import Theorems.Thm_D1Bound5_ordinaryLog10_mul
import Theorems.Thm_D1Bound5_ordinaryLog10_pow
import Theorems.Thm_D1Bound5_ordinaryLog10_strictMono
import Theorems.Thm_D1Bound5_ordinaryLog10_unit_parameters
import Theorems.Thm_D1Bound5_ordinary_height_envelope_from_orders

section
namespace D1Bound5

theorem unit_pair_residual_rate_lower (S : ℝ) (hS : 1000 ≤ S) :
    (2/5 : ℝ)*S^2 < 27*(S-1)^2/64 := by
  have hp := mul_nonneg (sub_nonneg.mpr hS)
    (show 0 ≤ S by linarith only [hS])
  nlinarith only [hp,hS]



/-- Specialization of the ordinary envelope to the unit-pair anchors.
The three logarithmic parameters are certified by exact power comparisons. -/
theorem _root_.solution (S D Z : ℝ)
    (hS : 10000 ≤ S) (hD : 0 < D) (hZ : 1 ≤ Z) (hprod : S*D < 2*Z^2)
    (horders : ∀ k : ℕ, 1 ≤ k →
      1 < 3*S*(42*S)^k/Z+Z/(2*(27*(S-1)^2/64)^k)) :
    ordinaryLog10 D < 7*ordinaryLog10 S+617/25+
      (118401/2500)/(ordinaryLog10 S-203/100) := by
  have hS0 : 0 < S := by linarith only [hS]
  have hS1 : 1 < S := by linarith only [hS]
  have hlogS : 4 ≤ ordinaryLog10 S := ordinaryLog10_ge_four hS
  obtain ⟨h42,h25,h253⟩ := ordinaryLog10_unit_parameters
  have hrate := unit_pair_residual_rate_lower S (by linarith only [hS])
  have hR : 0 < 27*(S-1)^2/64 :=
    (show 0 < (2/5 : ℝ)*S^2 by positivity).trans hrate
  have hHlog : ordinaryLog10 (42*1^3*S) < ordinaryLog10 S+(163/100 : ℝ) := by
    norm_num only [one_pow,mul_one]
    rw [ordinaryLog10_mul 42 S (by norm_num) hS0.ne']
    linarith only [h42]
  have hRlog : 2*ordinaryLog10 S-(2/5 : ℝ) < ordinaryLog10 (27*(S-1)^2/64) := by
    have h := ordinaryLog10_strictMono (by positivity : 0 < (2/5 : ℝ)*S^2) hrate
    rw [ordinaryLog10_mul (2/5) (S^2) (by norm_num) (by positivity),
      ordinaryLog10_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h,h25]
  have h := ordinary_height_envelope_from_orders 1 S D Z (27*(S-1)^2/64)
    (163/100) (-2/5) (241/100) (by norm_num) hS1 hD hZ hR hprod
    hHlog (by simpa only [sub_eq_add_neg,neg_div] using hRlog)
    (by simpa only [one_pow,mul_one] using h253)
    (by linarith only [hlogS]) (by linarith only [hlogS])
    (by intro k hk; simpa only [one_pow,mul_one,one_mul] using horders k hk)
  norm_num at h
  linarith only [h]



end D1Bound5
end
