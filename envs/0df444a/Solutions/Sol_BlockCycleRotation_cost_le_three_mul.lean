-- Prove2me | solution 1 for BlockCycleRotation.cost_le_three_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:23:58.143735+00:00
-- url     : https://prove2.me/submissions/22acd3ea-408a-40ea-a67f-1e808cd80576

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Euclid
import Theorems.Thm_BlockCycleRotation_moveCount_add_gcd_le
import Theorems.Thm_BlockCycleRotation_cost_add_gcd
import Mathlib


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

end BlockCycleRotation

open BlockCycleRotation in
/-- The block cycle algorithm never performs more than `3 * n` moves. -/
theorem solution {n k : ℕ} (h : 2 * k ≤ n) : cost n k ≤ 3 * n:= by
  have := cost_add_gcd_le h
  omega
