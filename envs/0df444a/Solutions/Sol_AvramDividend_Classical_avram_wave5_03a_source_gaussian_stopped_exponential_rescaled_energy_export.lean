-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_source_gaussian_stopped_exponential_rescaled_energy_export
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:48:55.099708+00:00
-- url     : https://prove2.me/submissions/36756f83-18e1-4d9b-b0d9-f821b5e6b011

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

/-- Exact source-stopped Gaussian exponential difference quotient energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, ((Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ) - 1) / θ) ^ 2 ∂P) =
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ ^ 2)) - 1) / θ ^ 2 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hψ :
      X.ψ (θ + θ) - X.ψ θ - X.ψ θ =
        X.σ ^ 2 * θ * θ := by
    simp only [SpectrallyNegativeLevy.ψ, hν,
      laplaceExponent_zero_jump_measure]
    ring
  let F : Ω → ℝ := fun ω =>
    Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ θ) - 1
  have hcross :
      (∫ ω, F ω * F ω ∂P) =
        Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * θ)) - 1 := by
    simpa only [F, hψ] using
      (levy_bounded_stopping_compensated_exp_centered_cross_moment
        X τ hτ T hbounded h θ θ hθ hθ)
  change (∫ ω, (F ω / θ) ^ 2 ∂P) =
    (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ ^ 2)) - 1) / θ ^ 2
  calc
    (∫ ω, (F ω / θ) ^ 2 ∂P) =
      ∫ ω, (F ω * F ω) / θ ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
    _ = (∫ ω, F ω * F ω ∂P) / θ ^ 2 := by
      simp only [div_eq_mul_inv, integral_mul_const]
    _ = (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * θ)) - 1) / θ ^ 2 := by
      rw [hcross]
    _ = (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ ^ 2)) - 1) / θ ^ 2 := by
      congr 2
      ring