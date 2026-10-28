-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_discounted_increment_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:55:59.04615+00:00
-- url     : https://prove2.me/submissions/ca746ba2-5ce7-4482-a958-ea734d1786cb

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- Discounted exponential moments of a future Lévy increment after bounded stopping. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, Real.exp (-(q * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P =
        Real.exp ((h : ℝ) * (X.ψ θ - q)) := by
  rw [integral_const_mul]
  rw [levy_bounded_stopping_increment_laplace X τ hτ T hbounded h θ hθ]
  rw [← Real.exp_add]
  congr 1
  ring
