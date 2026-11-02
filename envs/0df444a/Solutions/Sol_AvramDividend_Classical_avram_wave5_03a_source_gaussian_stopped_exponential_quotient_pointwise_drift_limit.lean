-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_source_gaussian_stopped_exponential_quotient_pointwise_drift_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:23:45.632747+00:00
-- url     : https://prove2.me/submissions/eb854148-f2ad-4a5e-8e55-01196b76d685

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_laplaceExponent_zero_jump_measure
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_exp_quadratic_secant_right_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Same source sample path: Gaussian exponential quotients converge to the drift-centred increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0) (h : ℝ≥0) (ω : Ω) :
    Filter.Tendsto
      (fun θ : ℝ =>
        (Real.exp (θ *
          (X.X (τ ω + h) ω - X.X (τ ω) ω) -
          (h : ℝ) * X.ψ θ) - 1) / θ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (X.X (τ ω + h) ω - X.X (τ ω) ω -
        (h : ℝ) * X.c)) := by
  let b : ℝ :=
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  let d : ℝ := -((h : ℝ) * X.σ ^ 2 / 2)
  have hψ (θ : ℝ) :
      X.ψ θ = X.c * θ + X.σ ^ 2 * θ ^ 2 / 2 := by
    simp only [SpectrallyNegativeLevy.ψ, hν,
      laplaceExponent_zero_jump_measure]
  have hexp (θ : ℝ) :
      θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ = b * θ + d * θ ^ 2 := by
    rw [hψ]
    dsimp [b, d]
    ring
  have hfun :
      (fun θ : ℝ => (Real.exp (θ *
        (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ) - 1) / θ) =
      (fun θ : ℝ => (Real.exp (b * θ + d * θ ^ 2) - 1) / θ) := by
    funext θ
    rw [hexp θ]
  rw [hfun]
  exact avram_wave5_03a_exp_quadratic_secant_right_limit b d
