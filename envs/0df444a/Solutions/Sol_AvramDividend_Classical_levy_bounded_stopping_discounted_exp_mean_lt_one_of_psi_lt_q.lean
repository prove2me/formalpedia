-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_lt_one_of_psi_lt_q
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:48:25.813154+00:00
-- url     : https://prove2.me/submissions/d2fa537e-ac97-4f0f-b387-f497e07ac816

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

/-- Strict exponential-mean contraction under discount exceeding the Lévy cumulant. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (hh : 0 < h) (θ q : ℝ) (hθ : 0 ≤ θ)
    (hlt : X.ψ θ < q) :
    ∫ ω, Real.exp (-(q * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P < 1 := by
  rw [levy_bounded_stopping_discounted_increment_laplace
    X τ hτ T hbounded h θ q hθ]
  have hhpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have harg : (h : ℝ) * (X.ψ θ - q) < 0 :=
    mul_neg_of_pos_of_neg hhpos (sub_neg.mpr hlt)
  have hExp := Real.exp_lt_exp.mpr harg
  simpa only [Real.exp_zero] using hExp
