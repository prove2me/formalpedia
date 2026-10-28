-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_ge_one_of_q_le_psi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:52:10.819522+00:00
-- url     : https://prove2.me/submissions/c997d568-6bfe-412b-8272-82e4e4b84ed6

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_increment_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- Lower exponential-moment bound when the Lévy cumulant dominates discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ) (hle : q ≤ X.ψ θ) :
    1 ≤ ∫ ω, Real.exp (-(q * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P := by
  rw [levy_bounded_stopping_discounted_increment_laplace
    X τ hτ T hbounded h θ q hθ]
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := NNReal.coe_nonneg h
  have harg : 0 ≤ (h : ℝ) * (X.ψ θ - q) :=
    mul_nonneg hh0 (sub_nonneg.mpr hle)
  have hexp := Real.exp_le_exp.mpr harg
  simpa only [Real.exp_zero] using hexp
