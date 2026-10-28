-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_compensated_increment_mean_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:34:28.371977+00:00
-- url     : https://prove2.me/submissions/eb6a821d-afff-4bb6-a050-a4a7fc915772

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- The Lévy exponential increment over a bounded stopping time has mean one after cumulant compensation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ θ) ∂P = 1 := by
  have hv := levy_bounded_stopping_increment_laplace X τ hτ T hbounded h θ hθ
  simp_rw [Real.exp_sub, div_eq_mul_inv]
  rw [integral_mul_const, hv]
  exact mul_inv_cancel₀ (Real.exp_ne_zero _)
