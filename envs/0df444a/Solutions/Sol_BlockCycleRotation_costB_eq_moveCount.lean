-- Prove2me | solution 1 for BlockCycleRotation.costB_eq_moveCount
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:14:20.781681+00:00
-- url     : https://prove2.me/submissions/68380af3-c5c4-46d6-8189-8e78aa374852

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

/-- The defining recursion, in the form we actually use. -/
theorem remSum_of_pos {k : ℕ} (n : ℕ) (hk : k ≠ 0) :
    remSum n k = k + remSum k (n % k) := by
  rw [remSum]; simp [hk]

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

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

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

@[simp]
theorem costB_zero (n b : ℕ) : costB n 0 b = 0 := by rw [costB]; simp

theorem costB_of_gt {n k b : ℕ} (hk : k ≠ 0) (h : b < k) :
    costB n k b = (n / k + 1) * k + costB (k + n % k) (n % k) b := by
  rw [costB]; simp [hk, Nat.not_le.2 h]

end BlockCycleRotation

open BlockCycleRotation in
/-- **Consistency of the two cost models.**  With no buffer, equation (integral)
computes exactly the move count `n - gcd(n,k) + 2·remSum(n,k)` of Lemma 12. -/
theorem solution : ∀ k n : ℕ, 2 * k ≤ n → costB n k 0 = moveCount n k:= by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hkn
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      rw [costB_zero]
      unfold moveCount
      simp
    · have hmod : n % k < k := Nat.mod_lt _ hk0
      have hIH := ih (n % k) hmod (k + n % k) (by omega)
      rw [costB_of_gt hk0.ne' hk0, hIH]
      -- the gcd is unchanged along the Euclidean step
      have hg1 : Nat.gcd n k = Nat.gcd k (n % k) := by
        rw [Nat.gcd_comm n k, Nat.gcd_rec k n]
        exact Nat.gcd_comm _ _
      have hg2 : Nat.gcd (k + n % k) (n % k) = Nat.gcd k (n % k) := gcd_add_left k (n % k)
      -- the remainder sums differ by the leading term `k`
      have hr : remSum (k + n % k) (n % k) = remSum k (n % k) := by
        rcases Nat.eq_zero_or_pos (n % k) with h0 | h0
        · rw [h0, remSum_zero, remSum_zero]
        · rw [remSum_of_pos _ h0.ne', remSum_of_pos _ h0.ne', Nat.add_mod_right]
      have hrs : remSum n k = k + remSum k (n % k) := remSum_of_pos n hk0.ne'
      -- the gcds are bounded by the array lengths
      have hgle : Nat.gcd n k ≤ n := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left n k)
      have hgle' : Nat.gcd (k + n % k) (n % k) ≤ k + n % k :=
        Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
      have hdm : n / k * k + n % k = n := Nat.div_add_mod' n k
      have hmul : (n / k + 1) * k = n / k * k + k := by ring
      unfold moveCount
      rw [hmul, hg2, hr, hrs, hg1]
      omega
