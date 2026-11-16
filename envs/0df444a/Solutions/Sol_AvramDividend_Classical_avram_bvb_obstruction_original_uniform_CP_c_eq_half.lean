-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_uniform_CP_c_eq_half
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:31:47.073791+00:00
-- url     : https://prove2.me/submissions/ce44cd50-c53a-40f1-ab51-42a85ec09202

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_negative_levy_mark_mean_half
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hc : X.c = 1 + (∫ z in Ioo (-1 : ℝ) 0,
      z ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)))) :
    X.c = 1 / 2 := by
  have hIntegral :
      (∫ z in Ioo (-1 : ℝ) 0,
        z ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))) =
        (-(1 / 2) : ℝ) := by
    change (∫ z, z ∂(((volume : Measure ℝ).restrict
      (Ioo (-1 : ℝ) 0)).restrict (Ioo (-1 : ℝ) 0))) = _
    rw [Measure.restrict_restrict measurableSet_Ioo, Set.inter_self]
    exact avram_bvb_obstruction_uniform_negative_levy_mark_mean_half
  rw [hc, hIntegral]
  ring
