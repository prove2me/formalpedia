-- Prove2me | solution 1 for AvramDividend.Classical.esscher_ordered_bounded_stops_history_future_increment_joint_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:58:33.683996+00:00
-- url     : https://prove2.me/submissions/fccecd35-f8f7-4773-b5cb-dbfc636c4b7a

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_future_increment_joint_product
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_observable_map_law

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
    {β : Type*} [MeasurableSpace β] (Y : Ω → β)
    (hY : Measurable Y)
    (hYτ : ∀ (B : Set β), MeasurableSet B →
      ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
        ((Y ⁻¹' B) ∩ {ω : Ω | τ ω ≤ s})) :
    let QT : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
    let QU : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    let Qτ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))
    Measure.map (fun ω : Ω => (Y ω,
      X.X (σ ω + u) ω - X.X (σ ω) ω)) QT =
      (Measure.map Y Qτ).prod (Measure.map (X.X u) QU) := by
  intro QT QU Qτ
  let Qσ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
    (Real.exp (θ * X.X (σ ω) ω -
      (σ ω : ℝ) * X.ψ θ)))
  have hboundτ : ∀ ω, τ ω ≤ H :=
    fun ω => (horder ω).trans (hboundσ ω)
  have hT' : H + 1 ≤ T := by
    calc
      H + 1 ≤ H + 1 + u :=
        le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ u from bot_le)
      _ ≤ T := hT
  have hYσ : ∀ (B : Set β), MeasurableSet B →
      ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
        ((Y ⁻¹' B) ∩ {ω : Ω | σ ω ≤ s}) := by
    intro B hB s
    have hσs : MeasurableSet[𝓕 s] {ω : Ω | σ ω ≤ s} := by
      simpa only [WithTop.coe_le_coe] using hstopσ s
    have hcut : (Y ⁻¹' B) ∩ {ω : Ω | σ ω ≤ s} =
        ((Y ⁻¹' B) ∩ {ω : Ω | τ ω ≤ s}) ∩
          {ω : Ω | σ ω ≤ s} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_setOf_eq]
      constructor
      · rintro ⟨hωY, hωσ⟩
        exact ⟨⟨hωY, (horder ω).trans hωσ⟩, hωσ⟩
      · rintro ⟨⟨hωY, _⟩, hωσ⟩
        exact ⟨hωY, hωσ⟩
    rw [hcut]
    exact (hYτ B hB s).inter hσs
  have hmσ : Measure.map Y QT = Measure.map Y Qσ :=
    esscher_bounded_stop_stoppedHistory_observable_map_law
      X θ hθ σ hstopσ H hboundσ T hT' Y hY hYσ
  have hmτ : Measure.map Y QT = Measure.map Y Qτ :=
    esscher_bounded_stop_stoppedHistory_observable_map_law
      X θ hθ τ hstopτ H hboundτ T hT' Y hY hYτ
  have hm : Measure.map Y Qσ = Measure.map Y Qτ :=
    hmσ.symm.trans hmτ
  calc
    Measure.map (fun ω : Ω => (Y ω,
        X.X (σ ω + u) ω - X.X (σ ω) ω)) QT =
      (Measure.map Y Qσ).prod (Measure.map (X.X u) QU) :=
        esscher_bounded_stop_stoppedHistory_future_increment_joint_product
          X θ hθ σ hstopσ H hboundσ u T hT Y hY hYσ
    _ = (Measure.map Y Qτ).prod (Measure.map (X.X u) QU) := by
      rw [hm]
