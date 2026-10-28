-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_stop_future_increment_stopped_likelihood_lintegral_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T19:12:46.283171+00:00
-- url     : https://prove2.me/submissions/7fa6ad9c-1988-4a15-b586-66db293a9849

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_lintegral_factor
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_density_eq
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω in A,
      g (X.X (τ ω + u) ω - X.X (τ ω) ω) ∂
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) A *
      (∫⁻ ω, g (X.X u ω) ∂
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))) := by
  have hT' : H + 1 ≤ T := by
    calc
      H + 1 ≤ H + 1 + u :=
        le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ u from bot_le)
      _ ≤ T := hT
  calc
    (∫⁻ ω in A,
      g (X.X (τ ω + u) ω - X.X (τ ω) ω) ∂
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
      (∫⁻ ω, g (X.X u ω) ∂
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))) :=
      esscher_bounded_stop_future_increment_lintegral_factor
        X θ hθ τ hstop H hbound u T hT A hA g hg
    _ = (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) A *
      (∫⁻ ω, g (X.X u ω) ∂
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))) := by
      rw [esscher_bounded_stop_stoppedHistory_density_eq
        X θ hθ τ hstop H hbound T hT' A hA]
