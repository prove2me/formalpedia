-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_increment_stationary_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:37:36.168058+00:00
-- url     : https://prove2.me/submissions/bdc40476-49cb-4b16-b02f-dd1acefdb5f1

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- The Laplace transform of the increment after a bounded stopping time equals its fixed-time counterpart. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P =
      ∫ ω, Real.exp (θ * X.X h ω) ∂P := by
  exact (levy_bounded_stopping_increment_laplace X τ hτ T hbounded h θ hθ).trans
    (X.laplace h θ hθ).2.symm
