-- Prove2me | solution 1 for AvramDividend.Classical.levy_exponential_conditional_growth_from_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T13:04:42.088876+00:00
-- url     : https://prove2.me/submissions/6eb4cb1b-0d0e-4f62-8446-129f33f638e7

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_exponential_conditional_semigroup
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_eigenfunction
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (θ q : ℝ)
    (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q) :
    ∀ᵐ ω ∂P,
      (P[(fun η => Real.exp (θ * X.X t η)) | 𝓕 s]) ω ≤
        Real.exp (θ * X.X s ω) *
          Real.exp (((t - s : ℝ≥0) : ℝ) * q) := by
  change laplaceExponent X.c X.σ X.ν θ ≤ q at hψ
  have hFac := levy_exponential_conditional_semigroup
    X s t hst θ hθ
  have hMoment :
      (∫ η, Real.exp (θ * X.X (t - s) η) ∂P) =
        Real.exp (((t - s : ℝ≥0) : ℝ) * laplaceExponent X.c X.σ X.ν θ) := by
    simpa only [zero_add, mul_zero, Real.exp_zero, one_mul] using
      (levy_transition_exponential_eigenfunction
        X (t - s) θ hθ 0)
  have ht : 0 ≤ ((t - s : ℝ≥0) : ℝ) := by positivity
  have htime :
      ((t - s : ℝ≥0) : ℝ) * laplaceExponent X.c X.σ X.ν θ ≤
        ((t - s : ℝ≥0) : ℝ) * q :=
    mul_le_mul_of_nonneg_left hψ ht
  have hExp :
      Real.exp (((t - s : ℝ≥0) : ℝ) * laplaceExponent X.c X.σ X.ν θ) ≤
        Real.exp (((t - s : ℝ≥0) : ℝ) * q) :=
    Real.exp_le_exp.mpr htime
  filter_upwards [hFac] with ω hω
  calc
    (P[(fun η => Real.exp (θ * X.X t η)) | 𝓕 s]) ω =
        Real.exp (θ * X.X s ω) *
          Real.exp (((t - s : ℝ≥0) : ℝ) * laplaceExponent X.c X.σ X.ν θ) := by
      rw [hω, hMoment]
    _ ≤ Real.exp (θ * X.X s ω) *
        Real.exp (((t - s : ℝ≥0) : ℝ) * q) :=
      mul_le_mul_of_nonneg_left hExp
        (Real.exp_nonneg (θ * X.X s ω))
