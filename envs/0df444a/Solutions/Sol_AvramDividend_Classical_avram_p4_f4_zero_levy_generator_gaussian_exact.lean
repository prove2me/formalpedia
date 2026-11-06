-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_zero_levy_generator_gaussian_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:51:59.887968+00:00
-- url     : https://prove2.me/submissions/18b73ff6-c152-4dac-88f6-20ad3eda1e23

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
    (hν : X.ν = 0) (w : ℝ → ℝ) (y : ℝ) :
    X.generator w y =
      X.σ ^ 2 / 2 * iteratedDeriv 2 w y + X.c * deriv w y := by
  simp [SpectrallyNegativeLevy.generator, hν]
