-- Prove2me | solution 1 for AvramDividend.Classical.esscher_ordered_bounded_stops_future_increment_earlier_history_map
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:51:13.219356+00:00
-- url     : https://prove2.me/submissions/3f3dabc0-35b2-4168-b7cc-f9711aaf66a0

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_stopped_likelihood_map_law
import Theorems.Thm_AvramDividend_Classical_esscher_ordered_bounded_stops_likelihood_history_consistency

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
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hAτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    let QT : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
    let QU : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    let Qτ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))
    Measure.map (fun ω : Ω => X.X (σ ω + u) ω -
        X.X (σ ω) ω) (QT.restrict A) =
      Qτ A • Measure.map (X.X u) QU := by
  intro QT QU Qτ
  let Qσ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
    (Real.exp (θ * X.X (σ ω) ω -
      (σ ω : ℝ) * X.ψ θ)))
  have hT' : H + 1 ≤ T := by
    calc
      H + 1 ≤ H + 1 + u :=
        le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ u from bot_le)
      _ ≤ T := hT
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
    exact (hAτ s).inter hσs
  have hOld : Qτ A = Qσ A :=
    esscher_ordered_bounded_stops_likelihood_history_consistency
      X θ hθ τ σ hstopτ hstopσ horder H hboundσ T hT' A hAτ
  calc
    Measure.map (fun ω : Ω => X.X (σ ω + u) ω -
        X.X (σ ω) ω) (QT.restrict A) =
      Qσ A • Measure.map (X.X u) QU :=
        esscher_bounded_stop_future_increment_stopped_likelihood_map_law
          X θ hθ σ hstopσ H hboundσ u T hT A hAσ
    _ = Qτ A • Measure.map (X.X u) QU := by
      rw [← hOld]
