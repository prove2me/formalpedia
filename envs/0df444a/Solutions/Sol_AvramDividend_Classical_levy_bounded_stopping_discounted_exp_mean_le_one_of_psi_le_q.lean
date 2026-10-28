-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_le_one_of_psi_le_q
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:44:21.514449+00:00
-- url     : https://prove2.me/submissions/12f39e8a-3126-4406-a490-02dbfac08da8

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

/-- Supermean bound for discounted Lévy exponentials under cumulant domination. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ) (hle : X.ψ θ ≤ q) :
    ∫ ω, Real.exp (-(q * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P ≤ 1 := by
  rw [levy_bounded_stopping_discounted_increment_laplace
    X τ hτ T hbounded h θ q hθ]
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := NNReal.coe_nonneg h
  have hexp : (h : ℝ) * (X.ψ θ - q) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hh0 (sub_nonpos.mpr hle)
  have hh := Real.exp_le_exp.mpr hexp
  simpa only [Real.exp_zero] using hh
