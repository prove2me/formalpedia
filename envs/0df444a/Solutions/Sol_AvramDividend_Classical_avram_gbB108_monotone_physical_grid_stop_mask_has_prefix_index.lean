-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB108_monotone_physical_grid_stop_mask_has_prefix_index
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:10:44.940371+00:00
-- url     : https://prove2.me/submissions/582130fd-5ba6-4abe-9d3f-d91ef96fe66f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
noncomputable section
/-- Every monotone physical grid has a finite prefix of pre-stop indices. -/
theorem solution (s : ℕ → ℝ≥0) (hs : Monotone s) (T : ℝ≥0)
    (m : ℕ) :
    ∃ k : ℕ, k ≤ m + 1 ∧
      ∀ i : ℕ, i < m + 1 → (s i < T ↔ i < k) := by
  induction m with
  | zero =>
      by_cases h0 : s 0 < T
      · refine ⟨1, by omega, ?_⟩
        intro i hi
        have hi0 : i = 0 := by omega
        subst i
        exact ⟨fun _ => by omega, fun _ => h0⟩
      · refine ⟨0, by omega, ?_⟩
        intro i hi
        have hi0 : i = 0 := by omega
        subst i
        exact ⟨fun h => (h0 h).elim, fun h => by omega⟩
  | succ m ih =>
      obtain ⟨k, hk, hiff⟩ := ih
      by_cases hlast : s (m + 1) < T
      · refine ⟨m + 2, by omega, ?_⟩
        intro i hi
        have hti : s i < T :=
          lt_of_le_of_lt (hs (by omega : i ≤ m + 1)) hlast
        exact ⟨fun _ => by omega, fun _ => hti⟩
      · refine ⟨k, by omega, ?_⟩
        intro i hi
        by_cases hiOld : i < m + 1
        · exact hiff i hiOld
        · have hieq : i = m + 1 := by omega
          subst i
          exact ⟨fun h => (hlast h).elim, fun h => by omega⟩
