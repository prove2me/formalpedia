-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f11_zero_jump_generator_eq_gaussian_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:39:45.529946+00:00
-- url     : https://prove2.me/submissions/34d3aae4-e626-403e-8de4-ae2cc3eaa1d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At zero Lévy measure the original generator has only its Gaussian
    second-order term and deterministic linear drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNu : X.ν = 0)
    (w : ℝ → ℝ) (y : ℝ) :
    X.generator w y = X.σ ^ 2 / 2 * iteratedDeriv 2 w y + X.c * deriv w y := by
  simp [SpectrallyNegativeLevy.generator, hNu]
