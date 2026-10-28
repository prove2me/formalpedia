-- Prove2me | solution 1 for AvramDividend.Classical.esscher_ordered_bounded_stops_likelihood_history_consistency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T19:19:07.148763+00:00
-- url     : https://prove2.me/submissions/b9de5e00-bf23-405a-8c38-975e181e936c

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
    (τ σ : Ω → ℝ≥0)
    (hstopτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (hstopσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ≥0)))
    (horder : ∀ ω, τ ω ≤ σ ω)
    (H : ℝ≥0) (hboundσ : ∀ ω, σ ω ≤ H)
    (T : ℝ≥0) (hT : H + 1 ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    let Qτ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))
    let Qσ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (σ ω) ω -
        (σ ω : ℝ) * X.ψ θ)))
    Qτ A = Qσ A := by
  intro Qτ Qσ
  have hboundτ : ∀ ω, τ ω ≤ H := by
    intro ω
    exact (horder ω).trans (hboundσ ω)
  have hAσ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s]
        (A ∩ {ω : Ω | σ ω ≤ s}) := by
    intro s
    have hσs : MeasurableSet[𝓕 s] {ω : Ω | σ ω ≤ s} := by
      simpa only [WithTop.coe_le_coe] using hstopσ s
    have hcut : A ∩ {ω : Ω | σ ω ≤ s} =
        (A ∩ {ω : Ω | τ ω ≤ s}) ∩
          {ω : Ω | σ ω ≤ s} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hωA, hωσ⟩
        exact ⟨⟨hωA, (horder ω).trans hωσ⟩, hωσ⟩
      · rintro ⟨⟨hωA, _⟩, hωσ⟩
        exact ⟨hωA, hωσ⟩
    rw [hcut]
    exact (hA s).inter hσs
  let QT : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
    (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
  have hτhistory : QT A = Qτ A :=
    esscher_bounded_stop_stoppedHistory_density_eq
      X θ hθ τ hstopτ H hboundτ T hT A hA
  have hσhistory : QT A = Qσ A :=
    esscher_bounded_stop_stoppedHistory_density_eq
      X θ hθ σ hstopσ H hboundσ T hT A hAσ
  exact hτhistory.symm.trans hσhistory
