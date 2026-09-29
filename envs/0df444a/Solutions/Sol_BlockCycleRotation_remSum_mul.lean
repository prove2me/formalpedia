-- Prove2me | solution 1 for BlockCycleRotation.remSum_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:14:08.261589+00:00
-- url     : https://prove2.me/submissions/f01dc78e-7f74-48f6-b7a2-327acf162312

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

end BlockCycleRotation

open BlockCycleRotation in
/-- **The remainder sum scales.** -/
theorem solution : ∀ k n d : ℕ, remSum (d * n) (d * k) = d * remSum n k:= by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n d
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; simp
    have hdk : d * k ≠ 0 := by positivity
    have hmod : d * n % (d * k) = d * (n % k) := by
      rw [Nat.mul_mod_mul_left]
    rw [remSum_of_pos _ hdk, remSum_of_pos n hk.ne', hmod,
      ih (n % k) (Nat.mod_lt _ hk) k d]
    ring
