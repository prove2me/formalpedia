-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb26_original_time_map_volume_Ioc_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:01:50.164021+00:00
-- url     : https://prove2.me/submissions/d76b164c-4629-4019-b760-57ca8d61518c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_time_map_finite_Ioc_preimage
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (s t T : ℝ≥0) (htT : t ≤ T) :
    (((volume : Measure ℝ).restrict (Icc (0 : ℝ) (T : ℝ))).map
      Real.toNNReal) (Ioc s t) =
    (volume : Measure ℝ) (Ioc (s : ℝ) (t : ℝ))  := by
  rw [Measure.map_apply measurable_real_toNNReal measurableSet_Ioc]
  rw [Measure.restrict_apply
    (measurableSet_Ioc.preimage measurable_real_toNNReal)]
  exact congrArg (volume : Measure ℝ)
    (avram_p3_b_bvjump_original_time_map_finite_Ioc_preimage s t T htT)
