-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger120_monotone_grid_first_crossing_index
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:47:21.441833+00:00
-- url     : https://prove2.me/submissions/7012e9a4-98d0-4f24-bb25-d93e18b6ca3f

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
noncomputable section

/-- A monotone grid starting below a positive stop must first reach it at one step. -/
theorem solution
    (v : ℕ → ℝ≥0) (hv : Monotone v)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hv0 : v 0 = 0)
    (N : ℕ) (hN : v N = ρ) :
    ∃ k : ℕ, k < N ∧ v k < ρ ∧ v (k + 1) = ρ := by
  have hfirst : ∀ M : ℕ, v M = ρ →
      ∃ k : ℕ, k < M ∧ v k < ρ ∧ v (k + 1) = ρ := by
    intro M
    induction M with
    | zero =>
        intro hzero
        have hz : (0 : ℝ≥0) = ρ := by simpa [hv0] using hzero
        exact False.elim ((ne_of_lt hρ) hz)
    | succ m ih =>
        intro hstop
        by_cases hbefore : v m < ρ
        · exact ⟨m, Nat.lt_succ_self m, hbefore, hstop⟩
        · have hle : v m ≤ ρ := by
            calc
              v m ≤ v (m + 1) := hv (Nat.le_succ m)
              _ = ρ := hstop
          have heq : v m = ρ := le_antisymm hle (le_of_not_gt hbefore)
          obtain ⟨k, hk, hlt, hnext⟩ := ih heq
          exact ⟨k, lt_trans hk (Nat.lt_succ_self m), hlt, hnext⟩
  exact hfirst N hN
