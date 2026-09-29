-- Prove2me | solution 1 for BlockCycleRotation.algCost_add_gcd_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:53:42.127151+00:00
-- url     : https://prove2.me/submissions/010bcdaa-81e8-4dca-9375-38b9f55aa403

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Average
import Definitions.Def_BlockCycleRotation_Euclid
import Theorems.Thm_BlockCycleRotation_moveCount_add_gcd_le
import Theorems.Thm_BlockCycleRotation_cost_add_gcd
import Theorems.Thm_BlockCycleRotation_gcd_min_eq
import Mathlib

open Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

/-- The algorithm's move count is the `moveCount` of `Euclid.lean`. -/
theorem cost_eq_moveCount {n k : ℕ} (hn : 0 < n) : cost n k = moveCount n k := by
  have hg : Nat.gcd n k ≤ n := Nat.le_of_dvd hn (Nat.gcd_dvd_left n k)
  have := cost_add_gcd k n
  simp only [moveCount]
  omega

/-- **Worst case, for the algorithm itself.**  For `2 * k ≤ n` the block cycle
algorithm performs at most `3 * (n - gcd n k)` moves. -/
theorem cost_add_gcd_le {n k : ℕ} (h : 2 * k ≤ n) :
    cost n k + 3 * Nat.gcd n k ≤ 3 * n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hk : k = 0 := by omega
    subst hn; subst hk; simp
  · rw [cost_eq_moveCount hn]
    exact moveCount_add_gcd_le h

/-- Whatever the shift, the shorter segment is at most half the array. -/
theorem two_mul_min_le {n k : ℕ} (h : k ≤ n) : 2 * min k (n - k) ≤ n := by omega

end BlockCycleRotation

open BlockCycleRotation in
/-- **Observation 2.**  The block cycle algorithm uses at most `3 * (n - gcd n k)`
moves, for *any* shift `k ≤ n` — the paper states it without restricting to
`2 * k ≤ n`.  Stated additively so that it holds with no truncated subtraction. -/
theorem solution {n k : ℕ} (h : k ≤ n) :
    algCost n k + 3 * Nat.gcd n k ≤ 3 * n:= by
  rw [algCost, ← gcd_min_eq h]
  exact cost_add_gcd_le (two_mul_min_le h)
