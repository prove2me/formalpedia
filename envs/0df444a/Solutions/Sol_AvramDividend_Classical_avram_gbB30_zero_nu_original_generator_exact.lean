-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB30_zero_nu_original_generator_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T17:57:24.151589+00:00
-- url     : https://prove2.me/submissions/fff1b639-7d31-4e58-ac5b-bf3ad548d1ed

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
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = (0 : Measure ℝ))
    (w : ℝ → ℝ) (y : ℝ) :
    X.GeneratorIntegrable w y ∧
      X.generator w y =
        X.σ ^ 2 / 2 * iteratedDeriv 2 w y +
        X.c * deriv w y := by 
  constructor
  · simpa [SpectrallyNegativeLevy.GeneratorIntegrable, IntegrableOn, hν] using
      (integrable_zero_measure : Integrable
        (generatorIntegrand w y) (0 : Measure ℝ))
  · simp [SpectrallyNegativeLevy.generator, hν]
