-- Prove2me | solution 1 for BlockCycleRotation.remSum_add_gcd_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:14:08.089817+00:00
-- url     : https://prove2.me/submissions/631ce52c-8d8d-4466-ae42-907a552d6de6

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
/-- **Master inequality.**  For all `n` and `k`,
`remSum n k + gcd n k ≤ 2 * k + n % k`.

This is the inductive engine behind the worst-case analysis.  Note it holds
unconditionally, including for `k = 0` (where both sides equal `n`). -/
theorem solution : ∀ k n : ℕ, remSum n k + Nat.gcd n k ≤ 2 * k + n % k:= by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    have hk0 : k ≠ 0 := hk.ne'
    have hrk : n % k < k := Nat.mod_lt _ hk
    -- `gcd n k = gcd k (n % k)`, matching one step of the Euclidean algorithm.
    have hgcd : Nat.gcd n k = Nat.gcd k (n % k) := by
      rw [Nat.gcd_comm n k, Nat.gcd_rec k n]
      exact Nat.gcd_comm _ _
    rw [remSum_of_pos n hk0, hgcd]
    rcases Nat.eq_zero_or_pos (n % k) with hr0 | hr0
    · -- `k` divides `n`: the algorithm stops here, and both sides equal `2 * k`.
      rw [hr0]
      simp only [remSum_zero, Nat.gcd_zero_right, add_zero]
      omega
    · -- The inductive step, applying the master inequality to `(k, n % k)`.
      have IH := ih (n % k) hrk k
      -- `n % k + k % (n % k) ≤ k`, because `k % (n % k) ≤ k - n % k`.
      have key : n % k + k % (n % k) ≤ k := by
        have h1 : k % (n % k) ≤ k - n % k := by
          rw [Nat.mod_eq_sub_mod hrk.le]
          exact Nat.mod_le _ _
        omega
      omega
