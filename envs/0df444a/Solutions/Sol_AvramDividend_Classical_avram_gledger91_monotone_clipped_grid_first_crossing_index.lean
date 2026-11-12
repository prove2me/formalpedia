-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger91_monotone_clipped_grid_first_crossing_index
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:12:57.052443+00:00
-- url     : https://prove2.me/submissions/8ef7ff64-7b31-4e80-b649-dc910c27b842

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
noncomputable section

theorem solution
    (v : ℕ → ℝ≥0) (hv : Monotone v) (ρ : ℝ≥0)
    (hv0 : v 0 < ρ) (N : ℕ) :
    v N = ρ → ∃ k : ℕ, k < N ∧ v k < ρ ∧ v (k + 1) = ρ := by
  induction N with
  | zero =>
      intro hzero
      exact False.elim ((ne_of_lt hv0) hzero)
  | succ N ih =>
      intro hend
      by_cases hpre : v N < ρ
      · exact ⟨N, Nat.lt_succ_self N, hpre, hend⟩
      · have hle : v N ≤ ρ := by
          calc
            v N ≤ v (N + 1) := hv (Nat.le_succ N)
            _ = ρ := hend
        have heq : v N = ρ := le_antisymm hle (le_of_not_gt hpre)
        obtain ⟨k, hk, hklt, hkeq⟩ := ih heq
        exact ⟨k, Nat.lt_succ_of_lt hk, hklt, hkeq⟩
