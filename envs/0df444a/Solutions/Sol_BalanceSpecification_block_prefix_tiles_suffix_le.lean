-- Prove2me | solution 1 for BalanceSpecification.block_prefix_tiles_suffix_le
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T02:17:08.229865+00:00
-- url     : https://prove2.me/submissions/ede86519-4b32-4721-97ea-dc2692612f49

import Mathlib
variable {H : ℕ → ℕ → ℝ}


theorem solution (hzero : ∀ s, H s 0 = 0)
    (hsub : ∀ s a b, H s (a + b) ≤ H s a + H (s + a) b)
    {r n k N : ℕ} (hfit : r + k * n ≤ N) :
    H 0 N ≤ H 0 r + (∑ j ∈ Finset.range k, H (r + j * n) n) +
      H (r + k * n) (N - (r + k * n)) := by
  have chain (k : ℕ) : H r (k*n) ≤ ∑ j ∈ Finset.range k, H (r+j*n) n := by
    induction k with
    | zero => simp [hzero]
    | succ k ih => rw [Nat.succ_mul, Finset.sum_range_succ]; exact (hsub r (k*n) n).trans (add_le_add ih le_rfl)
  have a := hsub 0 (r+k*n) (N-(r+k*n)); have b := hsub 0 r (k*n)
  rw [Nat.add_sub_of_le hfit] at a
  simp only [zero_add] at a b
  linarith [chain k]
