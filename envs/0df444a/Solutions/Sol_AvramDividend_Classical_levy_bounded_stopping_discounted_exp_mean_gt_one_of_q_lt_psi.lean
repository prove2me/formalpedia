-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_gt_one_of_q_lt_psi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:57:02.250007+00:00
-- url     : https://prove2.me/submissions/9a71c92a-c38b-4003-ad05-d9d6680f4289

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

/-- Strict exponential-mean growth when the Lévy cumulant exceeds the discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (hh : 0 < h) (θ q : ℝ) (hθ : 0 ≤ θ)
    (hlt : q < X.ψ θ) :
    1 < ∫ ω, Real.exp (-(q * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P := by
  rw [levy_bounded_stopping_discounted_increment_laplace
    X τ hτ T hbounded h θ q hθ]
  have hhpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have harg : 0 < (h : ℝ) * (X.ψ θ - q) :=
    mul_pos hhpos (sub_pos.mpr hlt)
  have hExp := Real.exp_lt_exp.mpr harg
  simpa only [Real.exp_zero] using hExp
