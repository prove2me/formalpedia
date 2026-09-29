-- Prove2me | solution 1 for BlockCycleRotation.cost_add_gcd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:22:36.886395+00:00
-- url     : https://prove2.me/submissions/94cbd95e-e099-47ae-892f-0a7a45fe5bc8

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Euclid
import Theorems.Thm_BlockCycleRotation_remSum_congr_mod
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

theorem cost_of_pos {k : ℕ} (n : ℕ) (hk : k ≠ 0) :
    cost n k = (n / k + 1) * k + cost (k + n % k) (n % k) := by
  rw [cost]; simp [hk]

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

/-- One Euclidean step, in the orientation we use throughout. -/
theorem gcd_step (n k : ℕ) : Nat.gcd n k = Nat.gcd k (n % k) := by
  rw [Nat.gcd_comm n k, Nat.gcd_rec k n]
  exact Nat.gcd_comm _ _

/-- Shifting the first argument by the second does not change the gcd. -/
theorem gcd_add_left (k r : ℕ) : Nat.gcd (k + r) r = Nat.gcd k r := by
  rw [Nat.gcd_comm (k + r) r, Nat.gcd_comm k r]
  exact Nat.gcd_add_self_right r k

/-- The step of the algorithm's recursion agrees with the Euclidean step. -/
theorem remSum_step {k r : ℕ} : remSum (k + r) r = remSum k r :=
  remSum_congr_mod (by simp [Nat.add_mod_right])

end BlockCycleRotation

open BlockCycleRotation in
/-- **Equation (12).**  The number of moves performed by the block cycle
algorithm is `n - gcd n k` moves of type B plus `2 * remSum n k` moves of type A.

Stated additively, so that it holds unconditionally (with no truncated
subtraction and no hypothesis relating `n` and `k`). -/
theorem solution : ∀ k n : ℕ, cost n k + Nat.gcd n k = n + 2 * remSum n k:= by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    have hk0 : k ≠ 0 := hk.ne'
    have hrk : n % k < k := Nat.mod_lt _ hk
    -- the recursive call, rewritten so both gcd and remSum refer to `(n, k)`
    have IH := ih (n % k) hrk (k + n % k)
    rw [gcd_add_left, ← gcd_step, remSum_step] at IH
    -- unfold one step of the algorithm and of `remSum`
    rw [cost_of_pos n hk0, remSum_of_pos n hk0]
    have hq : k * (n / k) + n % k = n := Nat.div_add_mod n k
    have hmul : (n / k + 1) * k = k * (n / k) + k := by ring
    rw [hmul]
    omega
