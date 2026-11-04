-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_weighted_log_inverse_for_negative_tests_all_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:06:38.462254+00:00
-- url     : https://prove2.me/submissions/8f77bab2-0bdf-441e-8539-13fddc1f00ef

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.SetSemiring
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_negative_mark_inverse_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

/-- The weighted logarithmic inverse recovers any test vanishing at nonnegative marks. -/
theorem solution
    (f : ℝ → ℝ) (hfpos : ∀ y : ℝ, 0 ≤ y → f y = 0) (y : ℝ) :
    (Real.exp y - 1) ^ 4 *
      (f (Real.log (Real.exp y)) / (Real.exp y - 1) ^ 4) = f y := by
  by_cases hy : y < 0
  · exact AvramDividend.Classical.avram_p2_b_rate_weighted_negative_mark_inverse_exact
      f y hy
  · have hnonneg : 0 ≤ y := le_of_not_gt hy
    simp [Real.log_exp, hfpos y hnonneg]
