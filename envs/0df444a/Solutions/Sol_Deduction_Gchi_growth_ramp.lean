-- Prove2me | solution 1 for Deduction.Gchi_growth_ramp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:17.968614+00:00
-- url     : https://prove2.me/submissions/1290a2f7-9539-431e-8e98-ec344e301be7

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_GchiGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {y : ℝ} (hy : 1 ≤ y) :
    ‖ramp f y‖ ≤ 2 * y ^ 2 := by
  have hy0 : 0 ≤ y := by linarith
  have key : ∀ n ∈ Finset.range (⌊y⌋₊ + 1),
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ)‖ ≤ y := by
    intro n _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hy0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_self hn'.le)
    have h0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have h2 : max (y / n - 1) 0 ≤ y / n := max_le (by linarith) (by positivity)
    have h3 : 0 ≤ max (y / n - 1) 0 := le_max_right _ _
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg h0,
      Real.norm_of_nonneg h3]
    calc _ ≤ (n : ℝ) * 1 * (y / n) := by
          gcongr
          exact hf n
      _ = y := by field_simp
  have h := (norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ key)
  rw [Finset.card_range, nsmul_eq_mul] at h
  have hfl : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  unfold ramp
  refine h.trans ?_
  push_cast
  nlinarith
end Deduction
