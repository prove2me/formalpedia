-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_stop_future_increment_terminal_consistency_map
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:46:43.601592+00:00
-- url     : https://prove2.me/submissions/fab22c41-407a-429d-9d27-a468ad04fd1d

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_stopped_likelihood_map_law
import Mathlib.Analysis.Complex.Exponential

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
    (u T₁ T₂ : ℝ≥0) (hT₁ : H + 1 + u ≤ T₁)
    (hT₂ : H + 1 + u ≤ T₂)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    let QT₁ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T₁ ω - (T₁ : ℝ) * X.ψ θ)))
    let QT₂ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T₂ ω - (T₂ : ℝ) * X.ψ θ)))
    Measure.map (fun ω : Ω => X.X (τ ω + u) ω - X.X (τ ω) ω)
      (QT₁.restrict A) =
    Measure.map (fun ω : Ω => X.X (τ ω + u) ω - X.X (τ ω) ω)
      (QT₂.restrict A) := by
  intro QT₁ QT₂
  let QU : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
    (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
  let QStop : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
    (Real.exp (θ * X.X (τ ω) ω -
      (τ ω : ℝ) * X.ψ θ)))
  have h₁ :
      Measure.map (fun ω : Ω => X.X (τ ω + u) ω -
        X.X (τ ω) ω) (QT₁.restrict A) =
      QStop A • Measure.map (X.X u) QU :=
    esscher_bounded_stop_future_increment_stopped_likelihood_map_law
      X θ hθ τ hstop H hbound u T₁ hT₁ A hA
  have h₂ :
      Measure.map (fun ω : Ω => X.X (τ ω + u) ω -
        X.X (τ ω) ω) (QT₂.restrict A) =
      QStop A • Measure.map (X.X u) QU :=
    esscher_bounded_stop_future_increment_stopped_likelihood_map_law
      X θ hθ τ hstop H hbound u T₂ hT₂ A hA
  exact h₁.trans h₂.symm
