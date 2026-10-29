-- Prove2me | solution 2 for AvramDividend.Classical.esscher_bounded_stop_joint_history_increment_terminal_consistency
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:48:23.790179+00:00
-- url     : https://prove2.me/submissions/9eaf8bf6-26f9-4287-83ce-a8a0bdfe4c9e

import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_future_increment_joint_product

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (u T₁ T₂ : ℝ≥0) (hT₁ : H + 1 + u ≤ T₁)
    (hT₂ : H + 1 + u ≤ T₂)
    {β : Type*} [MeasurableSpace β] (Y : Ω → β)
    (hY : Measurable Y)
    (hYstopped : ∀ (B : Set β), MeasurableSet B →
      ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
        ((Y ⁻¹' B) ∩ {ω : Ω | τ ω ≤ s})) :
    let QT₁ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T₁ ω - (T₁ : ℝ) * X.ψ θ)))
    let QT₂ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T₂ ω - (T₂ : ℝ) * X.ψ θ)))
    Measure.map (fun ω : Ω => (Y ω,
      X.X (τ ω + u) ω - X.X (τ ω) ω)) QT₁ =
    Measure.map (fun ω : Ω => (Y ω,
      X.X (τ ω + u) ω - X.X (τ ω) ω)) QT₂ := by
  intro QT₁ QT₂
  have h1 := esscher_bounded_stop_stoppedHistory_future_increment_joint_product X θ hθ τ hstop H hbound
    u T₁ hT₁ Y hY hYstopped
  have h2 := esscher_bounded_stop_stoppedHistory_future_increment_joint_product X θ hθ τ hstop H hbound
    u T₂ hT₂ Y hY hYstopped
  exact h1.trans h2.symm
