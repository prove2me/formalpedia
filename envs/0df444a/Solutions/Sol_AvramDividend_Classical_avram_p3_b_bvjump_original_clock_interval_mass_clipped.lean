-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_clock_interval_mass_clipped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:47:39.014097+00:00
-- url     : https://prove2.me/submissions/d8c10a52-5756-489b-af53-56ae51bce5a3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_clock_preimage_clipped_Ioc
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (s t T : ℝ≥0) :
    (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal) (Ioc s t) =
    (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal) (Ioc s (min t T)) := by
  have hm : Measurable Real.toNNReal :=
    continuous_real_toNNReal.measurable
  have hI : MeasurableSet (Ioc s t) := measurableSet_Ioc
  have hI' : MeasurableSet (Ioc s (min t T)) := measurableSet_Ioc
  calc
    (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal) (Ioc s t) =
        (volume : Measure ℝ)
          ((Real.toNNReal ⁻¹' Ioc s t) ∩ Icc 0 (T : ℝ)) := by
      rw [Measure.map_apply hm hI]
      rw [Measure.restrict_apply (hm hI)]
    _ = (volume : Measure ℝ)
          ((Real.toNNReal ⁻¹' Ioc s (min t T)) ∩ Icc 0 (T : ℝ)) := by
      rw [avram_p3_b_bvjump_original_clock_preimage_clipped_Ioc s t T]
    _ = (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal) (Ioc s (min t T)) := by
      rw [Measure.map_apply hm hI']
      rw [Measure.restrict_apply (hm hI')]
