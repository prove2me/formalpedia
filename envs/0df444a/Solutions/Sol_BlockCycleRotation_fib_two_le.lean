-- Prove2me | solution 1 for BlockCycleRotation.fib_two_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:23:58.250309+00:00
-- url     : https://prove2.me/submissions/f9e7a2cb-a127-4940-aafe-380cec35676c

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Euclid
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

end BlockCycleRotation

open BlockCycleRotation in
theorem solution {j : ℕ} : 2 ≤ Nat.fib (j + 3):= by
  have h : Nat.fib 3 ≤ Nat.fib (j + 3) := Nat.fib_mono (by omega)
  have h3 : Nat.fib 3 = 2 := by decide
  omega
