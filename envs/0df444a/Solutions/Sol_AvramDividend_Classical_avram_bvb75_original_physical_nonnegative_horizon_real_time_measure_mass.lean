-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb75_original_physical_nonnegative_horizon_real_time_measure_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:13:06.259023+00:00
-- url     : https://prove2.me/submissions/513915c5-2076-44aa-8cfc-7ae346d4ef9a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 ≤ T) :
    ((((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal).real Set.univ) = T := by
  have hMass :
      ((((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
        Set.univ) = ENNReal.ofReal T := by
    rw [Measure.map_apply measurable_real_toNNReal (by measurability)]
    simp [Real.volume_Icc]
  change (((((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    Set.univ).toReal) = T
  rw [hMass]
  exact ENNReal.toReal_ofReal hT
