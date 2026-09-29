-- Prove2me | solution 1 for BlockCycleRotation.remSum_congr_mod
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:17:32.227288+00:00
-- url     : https://prove2.me/submissions/03dbe9db-7bcf-4623-8486-cb8c78fbff52

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib


namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

/-- The defining recursion, in the form we actually use. -/
theorem remSum_of_pos {k : ℕ} (n : ℕ) (hk : k ≠ 0) :
    remSum n k = k + remSum k (n % k) := by
  rw [remSum]; simp [hk]

@[simp]
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **`remSum` only sees the first argument modulo the second.**

This is the content of the induction in the paper's proof of Lemma 12: the
algorithm's recursion and the Euclidean algorithm keep different first
components, but congruent ones, and so produce the same remainders. -/
theorem solution {n m k : ℕ} (h : n % k = m % k) : remSum n k = remSum m k:= by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [Nat.mod_zero] at h
    subst h
    rfl
  · rw [remSum_of_pos n hk.ne', remSum_of_pos m hk.ne', h]
