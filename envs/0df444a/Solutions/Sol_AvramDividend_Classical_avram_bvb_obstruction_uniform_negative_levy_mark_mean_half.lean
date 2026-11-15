-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_uniform_negative_levy_mark_mean_half
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T01:07:57.058954+00:00
-- url     : https://prove2.me/submissions/5c342769-86ce-47c8-af46-9ab06f474b15

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory intervalIntegral Set
theorem solution :
    (∫ z in Ioo (-1 : ℝ) 0, z ∂(volume : Measure ℝ)) =
      (-(1 / 2) : ℝ) := by
  rw [← integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 0)]
  rw [integral_id]
  norm_num
