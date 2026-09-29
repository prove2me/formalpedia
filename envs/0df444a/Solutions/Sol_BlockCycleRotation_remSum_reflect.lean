-- Prove2me | solution 1 for BlockCycleRotation.remSum_reflect
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:54:50.687897+00:00
-- url     : https://prove2.me/submissions/cc2b86f8-3000-4f7d-8299-2414b40fef1b

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_remSum_congr_mod
import Mathlib

open Filter Topology Finset Real

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

/-- The step of the algorithm's recursion agrees with the Euclidean step. -/
theorem remSum_step {k r : ℕ} : remSum (k + r) r = remSum k r :=
  remSum_congr_mod (by simp [Nat.add_mod_right])

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **The reflection.**  For `2k > n` the run on `(n,k)` yields `k` and then
repeats the run on `(n, n-k)`. -/
theorem solution {n k : ℕ} (hk : k ≤ n) (h : n < 2 * k) :
    remSum n k = k + remSum n (n - k):= by
  have hk0 : k ≠ 0 := by omega
  have hmod : n % k = n - k := by
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · simp
    · rw [Nat.mod_eq_sub_mod hk, Nat.mod_eq_of_lt (by omega)]
  have hstep : remSum n (n - k) = remSum k (n - k) := by
    have h1 : k + (n - k) = n := by omega
    calc remSum n (n - k) = remSum (k + (n - k)) (n - k) := by rw [h1]
      _ = remSum k (n - k) := remSum_step
  rw [remSum_of_pos n hk0, hmod, hstep]
