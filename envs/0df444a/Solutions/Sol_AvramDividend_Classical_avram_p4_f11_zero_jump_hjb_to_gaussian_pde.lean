-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f11_zero_jump_hjb_to_gaussian_pde
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:41:41.788608+00:00
-- url     : https://prove2.me/submissions/40c340a9-65d8-40ac-a27d-5e5cad6d5614

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The authentic source HJB drift bound specialises to the Gaussian PDE when the
    negative Lévy jump measure vanishes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNu : X.ν = 0)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hHJB : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.generator w y - q * w y ≤ 0) :
    ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.σ ^ 2 / 2 * iteratedDeriv 2 w y + X.c * deriv w y - q * w y ≤ 0 := by
  intro y hy hyC
  simpa [SpectrallyNegativeLevy.generator, hNu] using hHJB y hy hyC
