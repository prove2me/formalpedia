-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_CP_drift_one_from_triplet_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:26:22.251557+00:00
-- url     : https://prove2.me/submissions/fb90fd6e-37bb-4061-8106-d5f292f60d71

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hc : X.c = 1 +
      (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) :
    X.drift = 1 := by
  change X.c -
    (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) = 1
  rw [hc]
  ring
