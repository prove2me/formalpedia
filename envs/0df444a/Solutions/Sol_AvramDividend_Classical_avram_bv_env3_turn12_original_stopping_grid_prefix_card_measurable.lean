-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn12_original_stopping_grid_prefix_card_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:36:59.533062+00:00
-- url     : https://prove2.me/submissions/7d91fd77-5c56-4b65-914f-acafcc655e8f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The count of deterministic original Lévy grid points strictly before the
genuine stopping time is a measurable, bounded random index. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (m : ℕ) :
    Measurable (fun ω : Ω =>
      ((Finset.range m).filter
        (fun i => (u i : WithTop ℝ≥0) < τ ω)).card) ∧
    (∀ ω, ((Finset.range m).filter
      (fun i => (u i : WithTop ℝ≥0) < τ ω)).card ≤ m) := by
  classical
  have hSm (i : ℕ) :
      MeasurableSet {ω : Ω | (u i : WithTop ℝ≥0) < τ ω} :=
    (𝓕.rightCont).le (u i) _
      (avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
        X τ hStop u i)
  constructor
  · simp_rw [Finset.card_filter]
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite (hSm i) measurable_const measurable_const
  · intro ω
    have hs : ((Finset.range m).filter
        (fun i => (u i : WithTop ℝ≥0) < τ ω)) ⊆ Finset.range m :=
      Finset.filter_subset _ _
    exact (Finset.card_le_card hs).trans (by simp)
