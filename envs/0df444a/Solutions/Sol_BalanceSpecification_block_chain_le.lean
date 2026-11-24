-- Prove2me | solution 1 for BalanceSpecification.block_chain_le
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T02:10:45.290799+00:00
-- url     : https://prove2.me/submissions/f59e8489-30b4-4e7d-b3b6-1d00026ba242

import Mathlib
variable {H : ℕ → ℕ → ℝ}


theorem solution (hzero : ∀ s, H s 0 = 0)
    (hsub : ∀ s a b, H s (a + b) ≤ H s a + H (s + a) b) (s n k : ℕ) :
    H s (k * n) ≤ ∑ j ∈ Finset.range k, H (s + j * n) n := by
  induction k with
  | zero => simp [hzero]
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_succ]
    exact (hsub s (k*n) n).trans (add_le_add ih le_rfl)
