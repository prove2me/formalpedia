-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger97_crossing_grid_contact_sum_single_final_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:15:42.789971+00:00
-- url     : https://prove2.me/submissions/7acce59b-044c-4194-9254-b4cc0d456d8e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal
noncomputable section

/-! The original stopped grid has only one non-constant crossing cell. -/
theorem solution
    (w : ℝ → ℝ) (E : ℝ≥0 → ℝ) (v : ℕ → ℝ≥0)
    (Y Z : ℕ → ℝ) (k N : ℕ) (hkN : k < N)
    (hpost : ∀ i : ℕ, k < i → Y (i + 1) = Z i) :
    (∑ i ∈ Finset.range N, E (v (i + 1)) * (w (Y (i + 1)) - w (Z i))) =
      (∑ i ∈ Finset.range k, E (v (i + 1)) * (w (Y (i + 1)) - w (Z i))) +
        E (v (k + 1)) * (w (Y (k + 1)) - w (Z k)) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hk : k = N
    · subst N
      rw [Finset.sum_range_succ]
    · have hkN' : k < N := by omega
      rw [Finset.sum_range_succ, ih hkN']
      have hzero : E (v (N + 1)) *
          (w (Y (N + 1)) - w (Z N)) = 0 := by
        rw [hpost N hkN']
        ring
      rw [hzero, add_zero]
