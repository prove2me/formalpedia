-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_real_to_nonneg_clock_interval_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:25:53.500422+00:00
-- url     : https://prove2.me/submissions/0763f20a-c304-409d-93cc-f11cf9be3fbc

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_time_map_finite_Ioc_preimage
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (s t T : ℝ≥0) (htT : t ≤ T) :
    (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal) (Ioc s t) =
    ENNReal.ofReal ((t : ℝ) - (s : ℝ)) := by
  have hm : Measurable Real.toNNReal :=
    continuous_real_toNNReal.measurable
  have hI : MeasurableSet (Ioc s t) := measurableSet_Ioc
  calc
    (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal) (Ioc s t) =
        ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ)))
          (Real.toNNReal ⁻¹' Ioc s t) :=
      Measure.map_apply hm hI
    _ = (volume : Measure ℝ)
          ((Real.toNNReal ⁻¹' Ioc s t) ∩ Icc 0 (T : ℝ)) :=
      Measure.restrict_apply (hm hI)
    _ = (volume : Measure ℝ) (Ioc (s : ℝ) (t : ℝ)) := by
      rw [avram_p3_b_bvjump_original_time_map_finite_Ioc_preimage
        s t T htT]
    _ = ENNReal.ofReal ((t : ℝ) - (s : ℝ)) := by
      simp only [Real.volume_Ioc]
