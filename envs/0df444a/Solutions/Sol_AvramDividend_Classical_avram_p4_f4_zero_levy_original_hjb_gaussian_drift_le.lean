-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_zero_levy_original_hjb_gaussian_drift_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:53:26.383886+00:00
-- url     : https://prove2.me/submissions/13c00dee-6fc4-49ec-ab21-afcf78fa30b9

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
    (hν : X.ν = 0)
    (q : ℝ) (w : ℝ → ℝ) (y : ℝ)
    (hGen : X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0) :
    X.σ ^ 2 / 2 * iteratedDeriv 2 w y +
      X.c * deriv w y - q * w y ≤ 0 := by
  simpa [SpectrallyNegativeLevy.generator, hν] using hGen.2
