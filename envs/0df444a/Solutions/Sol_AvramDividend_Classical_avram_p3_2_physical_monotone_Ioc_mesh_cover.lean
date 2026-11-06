-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_physical_monotone_Ioc_mesh_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:50:54.966774+00:00
-- url     : https://prove2.me/submissions/6e5ec7e0-9b5f-44a7-80e4-3ab5e8736341

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- Every finite monotone stopped mesh partitions its total right-open
interval into adjacent half-open cells, including degenerate cells. -/
theorem solution
    (u : ℕ → ℝ) (hu : Monotone u) (n : ℕ) :
    (⋃ i ∈ Finset.range n, Ioc (u i) (u (i + 1))) =
      Ioc (u 0) (u n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      ext t
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_Ioc]
      constructor
      · rintro ⟨i, hi, hleft, hright⟩
        have h0i : u 0 ≤ u i := hu (Nat.zero_le i)
        have hiN : u (i + 1) ≤ u (n + 1) := by
          apply hu
          exact Nat.succ_le_succ (Nat.lt_succ_iff.mp hi)
        exact ⟨lt_of_le_of_lt h0i hleft, le_trans hright hiN⟩
      · rintro ⟨h0, hN⟩
        by_cases ht : t ≤ u n
        · have hmem : t ∈ Ioc (u 0) (u n) := ⟨h0, ht⟩
          rw [← ih] at hmem
          simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_Ioc] at hmem
          obtain ⟨i, hi, hleft, hright⟩ := hmem
          exact ⟨i, Nat.lt_trans hi (Nat.lt_succ_self n), hleft, hright⟩
        · exact ⟨n, Nat.lt_succ_self n, lt_of_not_ge ht, hN⟩
