-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_stop_stoppedEvent_density_eq_of_upper_grids
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T18:37:04.072527+00:00
-- url     : https://prove2.me/submissions/c3f949da-df2a-4800-94e3-9333457050ec

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_upper_stop_likelihood_uniformIntegrable
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_history_density_eq_of_ui_upper_grids


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (T H : ℝ≥0) (τ : Ω → ℝ≥0)
    (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0)
    (hgrid : ∀ n ω, τn n ω ∈ grid n)
    (hT : ∀ n s, s ∈ grid n → s ≤ T)
    (hstop : ∀ n s, s ∈ grid n →
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (hbound : ∀ n ω, τn n ω ≤ H)
    (hlim : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
    (habove : ∀ ω n, τ ω ≤ τn n ω)
    (A : Set Ω) (hA : MeasurableSet A)
    (hStopped : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A =
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) A := by
  have hUI : UniformIntegrable (fun n ω =>
      Real.exp (θ * X.X (τn n ω) ω -
        (τn n ω : ℝ) * X.ψ θ)) 1 P :=
    esscher_finite_grid_upper_stop_likelihood_uniformIntegrable
      X θ hθ T H τn grid hgrid hT hstop hbound
  have hHistory (n : ℕ) (s : ℝ≥0) (hs : s ∈ grid n) :
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τn n ω = s}) := by
    have hset : A ∩ {ω : Ω | τn n ω = s} =
        (A ∩ {ω : Ω | τ ω ≤ s}) ∩ {ω : Ω | τn n ω = s} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨ha, heq⟩
        exact ⟨⟨ha, le_trans (habove ω n) (le_of_eq heq)⟩, heq⟩
      · rintro ⟨⟨ha, _⟩, heq⟩
        exact ⟨ha, heq⟩
    rw [hset]
    exact (hStopped s).inter (hstop n s hs)
  exact esscher_bounded_stop_history_density_eq_of_ui_upper_grids
    X θ hθ T τ τn grid hgrid hT hstop hlim habove
    A hA hHistory hUI
