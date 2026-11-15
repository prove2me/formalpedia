-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_true_jump_support_reuse_horizon_for_all_earlier_mark_sums
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:13:18.843119+00:00
-- url     : https://prove2.me/submissions/20689e26-84e0-47c0-aa90-6af031754b23

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    (S_T S_t : Finset ℝ≥0) (z : ℝ≥0 → ℝ)
    (T t : ℝ≥0) (ht : t ≤ T)
    (hST : ∀ u : ℝ≥0, u ∈ S_T ↔ 0 < u ∧ u ≤ T ∧ z u ≠ 0)
    (hSt : ∀ u : ℝ≥0, u ∈ S_t ↔ 0 < u ∧ u ≤ t ∧ z u ≠ 0) :
    (∑ u ∈ S_t, if -1 < z u ∧ z u < 0 then z u else 0) =
    ∑ u ∈ S_T,
      if u ≤ t then (if -1 < z u ∧ z u < 0 then z u else 0) else 0 := by
  classical
  have hSet : S_t = S_T.filter (fun u => u ≤ t) := by
    ext u
    rw [hSt, Finset.mem_filter, hST]
    constructor
    · intro h
      exact ⟨⟨h.1, le_trans h.2.1 ht, h.2.2⟩, h.2.1⟩
    · intro h
      exact ⟨h.1.1, h.2, h.1.2.2⟩
  rw [hSet, Finset.sum_filter]
