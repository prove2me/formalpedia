-- Prove2me | solution 1 for AvramDividend.Classical.positive_grid_deficit_has_small_positive_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:31:02.480994+00:00
-- url     : https://prove2.me/submissions/6978a904-b8b3-4c43-b628-55ceb9c41793

import Mathlib.Data.Real.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A positive net drift deficit across a finite grid forces at least
    one strictly positive grid increment, retaining its uniform upper bound. -/
theorem solution
    (D : ℕ → ℝ) (N : ℕ) (b : ℝ)
    (hPositive : D 0 < D N)
    (hBound : ∀ k : ℕ, k < N →
      0 ≤ D (k + 1) - D k ∧ D (k + 1) - D k ≤ b) :
    ∃ k : ℕ, k < N ∧
      0 < D (k + 1) - D k ∧ D (k + 1) - D k ≤ b := by
  have hAdjacent (n : ℕ) :
      D 0 < D n → ∃ k : ℕ, k < n ∧ D k < D (k + 1) := by
    induction n with
    | zero =>
        intro h
        exact False.elim ((lt_irrefl (D 0)) h)
    | succ n ih =>
        intro h
        by_cases hLast : D n < D (n + 1)
        · exact ⟨n, Nat.lt_succ_self n, hLast⟩
        · have hPrior : D 0 < D n :=
            lt_of_lt_of_le h (le_of_not_gt hLast)
          obtain ⟨k, hk, hInc⟩ := ih hPrior
          exact ⟨k, Nat.lt_succ_of_lt hk, hInc⟩
  obtain ⟨k, hk, hInc⟩ := hAdjacent N hPositive
  exact ⟨k, hk, sub_pos.mpr hInc, (hBound k hk).2⟩
