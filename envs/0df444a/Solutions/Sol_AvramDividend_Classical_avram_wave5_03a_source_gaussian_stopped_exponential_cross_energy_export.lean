-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_source_gaussian_stopped_exponential_cross_energy_export
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:45:07.563942+00:00
-- url     : https://prove2.me/submissions/117b7b47-5277-402d-9098-7b3161c97d89

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_exp_centered_cross_moment
import Theorems.Thm_AvramDividend_Classical_laplaceExponent_zero_jump_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Original-path Gaussian second-moment identity, without any detached Brownian noise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    ∫ ω, (Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ) - 1) *
      (Real.exp (η *
        (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ η) - 1) ∂P =
      Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * η)) - 1 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hψ :
      X.ψ (θ + η) - X.ψ θ - X.ψ η =
        X.σ ^ 2 * θ * η := by
    simp only [SpectrallyNegativeLevy.ψ, hν,
      laplaceExponent_zero_jump_measure]
    ring
  simpa only [hψ] using
    (levy_bounded_stopping_compensated_exp_centered_cross_moment
      X τ hτ T hbounded h θ η hθ hη)
