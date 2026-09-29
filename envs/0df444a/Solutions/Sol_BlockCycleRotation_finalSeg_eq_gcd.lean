-- Prove2me | solution 1 for BlockCycleRotation.finalSeg_eq_gcd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:21:56.47472+00:00
-- url     : https://prove2.me/submissions/c7194c8f-75f1-4df1-a4a0-7171f1b06bd7

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

theorem finalSeg_of_pos {k : ℕ} (n : ℕ) (hk : k ≠ 0) :
    finalSeg n k = finalSeg (k + n % k) (n % k) := by
  rw [finalSeg]; simp [hk]

/-- One Euclidean step, in the orientation we use throughout. -/
theorem gcd_step (n k : ℕ) : Nat.gcd n k = Nat.gcd k (n % k) := by
  rw [Nat.gcd_comm n k, Nat.gcd_rec k n]
  exact Nat.gcd_comm _ _

/-- Shifting the first argument by the second does not change the gcd. -/
theorem gcd_add_left (k r : ℕ) : Nat.gcd (k + r) r = Nat.gcd k r := by
  rw [Nat.gcd_comm (k + r) r, Nat.gcd_comm k r]
  exact Nat.gcd_add_self_right r k

end BlockCycleRotation

open BlockCycleRotation in
/-- **Lemma 12(1).**  The block cycle algorithm terminates on a subproblem with
parameters `(gcd n k, 0)`. -/
theorem solution : ∀ k n : ℕ, finalSeg n k = Nat.gcd n k:= by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · rw [finalSeg_of_pos n hk.ne', ih (n % k) (Nat.mod_lt _ hk), gcd_add_left,
        ← gcd_step]
