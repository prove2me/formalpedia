-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_terminal_consistency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T19:22:08.953846+00:00
-- url     : https://prove2.me/submissions/6042bb19-b511-4c16-b79e-430725d6ff2a

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_density_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (T₁ T₂ : ℝ≥0) (hT₁ : H + 1 ≤ T₁)
    (hT₂ : H + 1 ≤ T₂)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T₁ ω - (T₁ : ℝ) * X.ψ θ)))) A =
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T₂ ω - (T₂ : ℝ) * X.ψ θ)))) A := by
  let QStop : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
    (Real.exp (θ * X.X (τ ω) ω -
      (τ ω : ℝ) * X.ψ θ)))
  have h₁ :
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X T₁ ω - (T₁ : ℝ) * X.ψ θ)))) A =
      QStop A :=
    esscher_bounded_stop_stoppedHistory_density_eq
      X θ hθ τ hstop H hbound T₁ hT₁ A hA
  have h₂ :
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X T₂ ω - (T₂ : ℝ) * X.ψ θ)))) A =
      QStop A :=
    esscher_bounded_stop_stoppedHistory_density_eq
      X θ hθ τ hstop H hbound T₂ hT₂ A hA
  exact h₁.trans h₂.symm
