-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_dominated_martingale_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T22:14:07.411685+00:00
-- url     : https://prove2.me/submissions/e0a03e15-020b-4fc1-bdf5-1605661f9c5e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ja18_integrable_of_dom_ae_grid_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A uniformly integrable physical-cutoff martingale family converges
to an adapted martingale on the same right-continuous filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (J : ℕ → ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → ℝ)
    (hInt : ∀ k t, Integrable (J k t) P)
    (hMart : ∀ (k : ℕ) (s t : ℝ≥0), s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (J k t) ω = J k s ω)
    (hLimit : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k => J k t ω) atTop (𝓝 (Z t ω)))
    (hSelf : ∀ t : ℝ≥0, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont t) P (Z t) ω = Z t ω)
    (hBounds : ∀ T : ℝ≥0, ∃ B : Ω → ℝ,
      Integrable B P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T → ‖Z t ω‖ ≤ B ω) ∧
      (∀ k : ℕ, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
        ‖J k t ω‖ ≤ B ω)) :
    (∀ t : ℝ≥0, Integrable (Z t) P) ∧
    (∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (Z t) ω = Z s ω) := by
  have hZInt : ∀ t : ℝ≥0, Integrable (Z t) P := by
    intro t
    obtain ⟨B, hBi, hZd, _⟩ := hBounds t
    have hlim : ∀ᵐ ω ∂P,
        Tendsto (fun k => J k t ω) atTop (𝓝 (Z t ω)) := by
      filter_upwards [hLimit] with ω hw
      exact hw t
    have hDom : ∀ᵐ ω ∂P, ‖Z t ω‖ ≤ B ω := by
      filter_upwards [hZd] with ω hw
      exact hw t le_rfl
    exact avram_ja18_integrable_of_dom_ae_grid_limit
      (fun k => J k t) (Z t) B (fun k => hInt k t) hlim hBi hDom
  refine ⟨hZInt, ?_⟩
  intro s t hst
  obtain ⟨B, hBi, _, hJd⟩ := hBounds t
  have htd : ∀ k, ∀ᵐ ω ∂P, ‖J k t ω‖ ≤ B ω := by
    intro k
    filter_upwards [hJd k] with ω hw
    exact hw t le_rfl
  have hsd : ∀ k, ∀ᵐ ω ∂P, ‖J k s ω‖ ≤ B ω := by
    intro k
    filter_upwards [hJd k] with ω hw
    exact hw s hst
  have hlimT : ∀ᵐ ω ∂P,
      Tendsto (fun k => J k t ω) atTop (𝓝 (Z t ω)) := by
    filter_upwards [hLimit] with ω hw
    exact hw t
  have hlimS : ∀ᵐ ω ∂P,
      Tendsto (fun k => J k s ω) atTop (𝓝 (Z s ω)) := by
    filter_upwards [hLimit] with ω hw
    exact hw s
  have hEq : ∀ k,
      (P[J k t | 𝓕.rightCont s]) =ᵐ[P]
      (P[J k s | 𝓕.rightCont s]) := by
    intro k
    filter_upwards [hMart k s t hst, hMart k s s le_rfl] with ω ht hs
    exact ht.trans hs.symm
  have h := tendsto_condExp_unique
    (fs := fun k => J k t) (gs := fun k => J k s)
    (f := Z t) (g := Z s)
    (fun k => hInt k t) (fun k => hInt k s)
    hlimT hlimS B hBi B hBi htd hsd hEq
  filter_upwards [h, hSelf s] with ω hω hsω
  exact hω.trans hsω
