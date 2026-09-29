-- Prove2me | solution 1 for BlockCycleRotation.moveCount_fib
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:18:50.072906+00:00
-- url     : https://prove2.me/submissions/433369d7-701e-4edd-81fd-cbabf3a506ba

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Euclid
import Theorems.Thm_BlockCycleRotation_remSum_fib
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

/-- Shifting the first argument by the second does not change the gcd. -/
theorem gcd_add_left (k r : ℕ) : Nat.gcd (k + r) r = Nat.gcd k r := by
  rw [Nat.gcd_comm (k + r) r, Nat.gcd_comm k r]
  exact Nat.gcd_add_self_right r k

theorem gcd_fib_add_two (m : ℕ) : Nat.gcd (Nat.fib (m + 2)) (Nat.fib m) = 1 := by
  have hsplit : Nat.fib (m + 2) = Nat.fib (m + 1) + Nat.fib m := by
    rw [Nat.fib_add_two]; ring
  rw [hsplit, gcd_add_left]
  exact (Nat.fib_coprime_fib_succ m).symm

end BlockCycleRotation

open BlockCycleRotation in
/-- **Observation 6, the Fibonacci family.**  At `n = F_{m+2}`, `k = F_m` (`m ≥ 2`)
the algorithm uses `3n - 5 = 3n - 3gcd(n,k) - 2` moves, two short of the
worst-case bound `3n - 3gcd(n,k)` of Theorem A. -/
theorem solution (j : ℕ) :
    moveCount (Nat.fib (j + 4)) (Nat.fib (j + 2)) = 3 * Nat.fib (j + 4) - 5:= by
  have hg : Nat.gcd (Nat.fib (j + 4)) (Nat.fib (j + 2)) = 1 := by
    have h := gcd_fib_add_two (m := j + 2)
    have e : j + 2 + 2 = j + 4 := by omega
    rwa [e] at h
  have hr : remSum (Nat.fib (j + 4)) (Nat.fib (j + 2)) = Nat.fib (j + 4) - 2 := remSum_fib j
  have hpos : 3 ≤ Nat.fib (j + 4) := by
    have h : Nat.fib 4 ≤ Nat.fib (j + 4) := Nat.fib_mono (by omega)
    have h4 : Nat.fib 4 = 3 := by decide
    omega
  unfold moveCount
  rw [hg, hr]
  omega
