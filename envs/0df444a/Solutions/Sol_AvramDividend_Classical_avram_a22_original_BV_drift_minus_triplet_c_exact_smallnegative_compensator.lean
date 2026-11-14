-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_BV_drift_minus_triplet_c_exact_smallnegative_compensator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T16:09:08.394361+00:00
-- url     : https://prove2.me/submissions/234ef786-31e4-4935-b3b0-c1ced0c882c6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The genuine original triplet uses a strict negative smallmark compensation band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    X.drift - X.c =
      -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) := by
  change X.c - (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) - X.c =
    -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)
  ring
