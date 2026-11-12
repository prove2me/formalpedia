-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b21_original_time_map_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:16:30.74798+00:00
-- url     : https://prove2.me/submissions/8cd8b7ff-c850-409d-b803-8a00d44e701d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Transport the exact original physical compensator time measure. -/
theorem solution (T : ℝ) (f : ℝ≥0 → ℝ)
    (hf : AEStronglyMeasurable f
      (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) :
    (∫ t : ℝ≥0, f t ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) =
      ∫ t in Icc (0 : ℝ) T, f (Real.toNNReal t) := by
  exact integral_map continuous_real_toNNReal.measurable.aemeasurable hf
