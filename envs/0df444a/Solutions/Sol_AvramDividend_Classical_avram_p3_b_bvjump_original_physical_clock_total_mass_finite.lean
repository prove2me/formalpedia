-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_physical_clock_total_mass_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:05:04.533974+00:00
-- url     : https://prove2.me/submissions/3c1e0121-e8df-4412-9080-297487093d85

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- The exact finite physical clock in the source compensated jump theorem has finite mass. -/
theorem solution (T : ℝ≥0) :
    (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal) Set.univ < ∞ := by
  have hm : Measurable Real.toNNReal :=
    continuous_real_toNNReal.measurable
  rw [Measure.map_apply hm MeasurableSet.univ]
  simp only [preimage_univ]
  rw [Measure.restrict_apply MeasurableSet.univ]
  simpa [Real.volume_Icc] using
    (show (volume : Measure ℝ) (Icc 0 (T : ℝ)) < ∞ by
      simp [Real.volume_Icc])
