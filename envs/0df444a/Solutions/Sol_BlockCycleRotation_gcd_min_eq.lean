-- Prove2me | solution 1 for BlockCycleRotation.gcd_min_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:52:19.77592+00:00
-- url     : https://prove2.me/submissions/a292c2f2-f4a7-4c55-b165-77483de4fc64

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Euclid
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

end BlockCycleRotation

open BlockCycleRotation in
/-- `gcd` does not see the reflection the algorithm applies to the shift. -/
theorem solution {n k : ℕ} (h : k ≤ n) : Nat.gcd n (min k (n - k)) = Nat.gcd n k:= by
  rcases le_total k (n - k) with hk | hk
  · rw [min_eq_left hk]
  · rw [min_eq_right hk, Nat.gcd_comm n (n - k), Nat.gcd_comm n k]
    exact Nat.gcd_self_sub_left h
