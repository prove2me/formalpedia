-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva20_halfopen_monotone_grid_step_select
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:09:19.98491+00:00
-- url     : https://prove2.me/submissions/6732126a-dd9e-4a2a-a338-12a0cf736b57

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

/-- The coefficient at the unique occupied half-open cell is the step-function value. -/
theorem solution
    (n i : ℕ) (hi : i < n + 1) (u : ℕ → ℝ)
    (hu : StrictMono u) (c : ℕ → ℝ) (t : ℝ)
    (ht : t ∈ Set.Ico (u i) (u (i + 1))) :
    (∑ j ∈ Finset.range (n + 1),
      (Set.Ico (u j) (u (j + 1))).indicator (fun _ => c j) t) = c i := by
  classical
  have hnot (j : ℕ) (hji : j ≠ i) :
      t ∉ Ico (u j) (u (j + 1)) := by
    intro hj
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · have hle : j + 1 ≤ i := Nat.succ_le_iff.mpr hlt
      exact (not_lt_of_ge ((hu.monotone hle).trans ht.1)) hj.2
    · have hle : i + 1 ≤ j := Nat.succ_le_iff.mpr hgt
      exact (not_lt_of_ge ((hu.monotone hle).trans hj.1)) ht.2
  have hsum :
      (∑ j ∈ Finset.range (n + 1),
        (Ico (u j) (u (j + 1))).indicator (fun _ => c j) t) =
        (Ico (u i) (u (i + 1))).indicator (fun _ => c i) t := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      simp [Set.indicator, hnot j hji]
    · intro hni
      exact (hni (Finset.mem_range.mpr hi)).elim
  simpa [Set.indicator, ht] using hsum
