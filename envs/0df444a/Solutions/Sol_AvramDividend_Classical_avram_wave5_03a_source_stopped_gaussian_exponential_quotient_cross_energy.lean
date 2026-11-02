-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_source_stopped_gaussian_exponential_quotient_cross_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:09:16.647626+00:00
-- url     : https://prove2.me/submissions/aa7b03d2-5a92-4e77-8967-1b482f9a40d0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_gaussian_stopped_exponential_cross_energy_export

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Same-path stopped Gaussian difference quotients have the exact cross-energy kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    (∫ ω, ((Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ) - 1) / θ) *
      ((Real.exp (η *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ η) - 1) / η) ∂P) =
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * η)) - 1) / (θ * η) := by
  have hcross :=
    avram_wave5_03a_source_gaussian_stopped_exponential_cross_energy_export
      X hν τ hτ T hbounded h θ η hθ hη
  calc
    (∫ ω, ((Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ) - 1) / θ) *
      ((Real.exp (η *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ η) - 1) / η) ∂P) =
      (∫ ω, ((Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ) - 1) *
        (Real.exp (η *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ η) - 1)) / (θ * η) ∂P) := by
          apply integral_congr_ae
          filter_upwards [] with ω
          ring
    _ = (∫ ω, ((Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ) - 1) *
        (Real.exp (η *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ η) - 1)) ∂P) / (θ * η) := by
          simp only [div_eq_mul_inv, integral_mul_const]
    _ = (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * η)) - 1) /
        (θ * η) := by
      rw [hcross]