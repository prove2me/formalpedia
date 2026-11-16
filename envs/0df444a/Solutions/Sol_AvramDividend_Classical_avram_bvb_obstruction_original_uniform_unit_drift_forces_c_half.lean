-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_uniform_unit_drift_forces_c_half
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:59:02.266548+00:00
-- url     : https://prove2.me/submissions/edd2524b-dc2e-4697-8e58-9b1fddae0639

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_CP_c_eq_half
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))
    (hDrift : X.drift = 1) :
    X.c = 1 / 2 := by
  have hc : X.c = 1 +
      (∫ z in Ioo (-1 : ℝ) 0, z ∂
        ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))) := by
    change X.c -
      (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) = 1 at hDrift
    rw [hν] at hDrift
    linarith
  exact avram_bvb_obstruction_original_uniform_CP_c_eq_half X hc
