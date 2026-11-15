-- Prove2me | solution 1 for AvramDividend.Classical.avram_a31_physical_jump_accumulator_horizon_consistency_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:30:08.8293+00:00
-- url     : https://prove2.me/submissions/f907635c-e11c-45ca-b03a-fd5585368375

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal BigOperators
noncomputable section

/-- Finite physical marked jump accumulators are compatible across nested time horizons. -/
theorem solution
    (a : ℝ≥0 → ℝ) (T U : ℝ≥0) (hTU : T ≤ U)
    (S R : Finset ℝ≥0)
    (hS : ∀ u, u ∈ S ↔ 0 < u ∧ u ≤ T ∧ a u ≠ 0)
    (hR : ∀ u, u ∈ R ↔ 0 < u ∧ u ≤ U ∧ a u ≠ 0) :
    ∀ t : ℝ≥0, t ≤ T →
      (∑ u ∈ S, if u ≤ t then a u else 0) =
      (∑ u ∈ R, if u ≤ t then a u else 0) := by
  classical
  have hSubset : S ⊆ R := by
    intro u hu
    obtain ⟨hu0, huT, hnonzero⟩ := (hS u).mp hu
    exact (hR u).mpr ⟨hu0, le_trans huT hTU, hnonzero⟩
  intro t ht
  apply Finset.sum_subset hSubset
  intro u huR huNot
  by_cases hut : u ≤ t
  · obtain ⟨hu0, _, hnonzero⟩ := (hR u).mp huR
    have huS : u ∈ S := (hS u).mpr ⟨hu0, le_trans hut ht, hnonzero⟩
    exact (huNot huS).elim
  · simp [hut]
