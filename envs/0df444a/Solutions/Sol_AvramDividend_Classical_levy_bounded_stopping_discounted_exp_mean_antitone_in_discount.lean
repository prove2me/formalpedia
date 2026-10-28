-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_antitone_in_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:11:59.0431+00:00
-- url     : https://prove2.me/submissions/dd372106-d543-4f22-99c1-c43fd532acbd

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_increment_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- Increasing the discount decreases the expected discounted exponential of a bounded-stopping-time Lévy increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ q₁ q₂ : ℝ) (hθ : 0 ≤ θ) (hq : q₁ ≤ q₂) :
    (∫ ω, Real.exp (-(q₂ * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P) ≤
    ∫ ω, Real.exp (-(q₁ * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P := by
  rw [levy_bounded_stopping_discounted_increment_laplace
    X τ hτ T hbounded h θ q₂ hθ,
    levy_bounded_stopping_discounted_increment_laplace
    X τ hτ T hbounded h θ q₁ hθ]
  apply Real.exp_le_exp.mpr
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := NNReal.coe_nonneg h
  have hdiff : X.ψ θ - q₂ ≤ X.ψ θ - q₁ := by linarith
  exact mul_le_mul_of_nonneg_left hdiff hh0
