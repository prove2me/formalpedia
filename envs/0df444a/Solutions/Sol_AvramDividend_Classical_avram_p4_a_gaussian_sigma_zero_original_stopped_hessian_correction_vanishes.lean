-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_sigma_zero_original_stopped_hessian_correction_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:51:10.251797+00:00
-- url     : https://prove2.me/submissions/8a60a81e-e72e-4c9a-98cd-7f912614c565

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

/-- In the original pure-jump Gaussian-variance-zero branch, the entire
discounted continuous Itô Hessian correction is zero on any stopped clock.
No Brownian process, global C² regularity, or boundary occupation input is needed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : X.σ = 0)
    (q : ℝ) (w : ℝ → ℝ) (U : ℝ≥0 → ℝ)
    (μ : Measure ℝ≥0) (τ : ℝ≥0) :
    (∫ s, Real.exp (-(q * (s : ℝ))) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (U s))
      ∂(μ.restrict (Iio τ))) = 0 := by
  simp [hσ]
