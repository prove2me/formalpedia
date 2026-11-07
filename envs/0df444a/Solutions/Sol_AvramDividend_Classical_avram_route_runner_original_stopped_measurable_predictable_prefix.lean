-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_runner_original_stopped_measurable_predictable_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:12:02.892598+00:00
-- url     : https://prove2.me/submissions/02ee8f9a-9d1e-4078-b8cf-8a86cf7453da

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_stopped_grid_predictable_initial_segment
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_nat_prefix_all_preimages_measurable
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_rightcont_prefix_to_ambient
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual stopped physical grid has a bounded predictable measurable prefix. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ) :
    ∃ k : Ω → ℕ,
      (∀ ω, k ω ≤ m) ∧
      (∀ ω i, i < m →
        ((u i : WithTop ℝ≥0) < τ ω ↔ i < k ω)) ∧
      (∀ i, MeasurableSet[𝓕.rightCont (u i)]
        {ω : Ω | i < k ω}) ∧
      (∀ s : Set ℕ, MeasurableSet (k ⁻¹' s)) := by
  obtain ⟨k, hkBound, hMask, hPredict⟩ :=
    avram_route_runner_stopped_grid_predictable_initial_segment
      X τ hStop u hu m
  have hAmbient : ∀ i, MeasurableSet {ω : Ω | i < k ω} :=
    avram_route_runner_rightcont_prefix_to_ambient u k hPredict
  have hAll : ∀ s : Set ℕ, MeasurableSet (k ⁻¹' s) :=
    avram_route_runner_nat_prefix_all_preimages_measurable k hAmbient
  exact ⟨k, hkBound, hMask, hPredict, hAll⟩
