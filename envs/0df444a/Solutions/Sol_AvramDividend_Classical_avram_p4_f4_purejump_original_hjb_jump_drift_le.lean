-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_purejump_original_hjb_jump_drift_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:09:42.359206+00:00
-- url     : https://prove2.me/submissions/c3603e2b-2ac3-4d02-bc26-847b6feff1b2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : X.σ = 0)
    (q : ℝ) (w : ℝ → ℝ) (y : ℝ)
    (hGen : X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0) :
    X.c * deriv w y +
      (∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) -
        q * w y ≤ 0 := by
  simpa [SpectrallyNegativeLevy.generator, hσ] using hGen.2
