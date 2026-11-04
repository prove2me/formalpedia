-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_clock_after_horizon_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:38:28.227285+00:00
-- url     : https://prove2.me/submissions/19436569-6bbb-45e1-8248-83f26db1c289

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_clock_after_horizon_preimage_empty
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (s t T : ℝ≥0) (hTs : T ≤ s) :
    (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal) (Ioc s t) = 0 := by
  have hm : Measurable Real.toNNReal :=
    continuous_real_toNNReal.measurable
  have hI : MeasurableSet (Ioc s t) := measurableSet_Ioc
  rw [Measure.map_apply hm hI]
  rw [Measure.restrict_apply (hm hI)]
  rw [avram_p3_b_bvjump_original_clock_after_horizon_preimage_empty
    s t T hTs]
  exact measure_empty
