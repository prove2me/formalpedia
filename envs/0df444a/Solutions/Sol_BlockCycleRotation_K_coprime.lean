-- Prove2me | solution 1 for BlockCycleRotation.K_coprime
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:45:19.344016+00:00
-- url     : https://prove2.me/submissions/7edf655c-4b22-4c86-a8c4-c4c3d76c6df4

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_K_append
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

/-- The mirrored recursion: appending an entry at the end. -/
theorem K_concat (l : List ℕ) (h : l ≠ []) (c : ℕ) :
    K (l ++ [c]) = c * K l + K l.dropLast := by
  rw [K_append l [c] h (by simp)]
  simp [Nat.mul_comm]

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **Consecutive continuants are coprime**: `gcd (K l) (K l.dropLast) = 1`.

This supplies the condition `gcd(a, a') = 1` in Heilbronn's correspondence. -/
theorem solution : ∀ l : List ℕ, Nat.gcd (K l) (K l.dropLast) = 1:= by
  intro l
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton m c ih =>
    by_cases hm : m = []
    · subst hm; simp
    · have hdl : (m ++ [c]).dropLast = m := by simp
      rw [K_concat m hm c, hdl, Nat.add_comm, Nat.mul_comm c (K m),
        Nat.gcd_add_mul_left_left, Nat.gcd_comm]
      exact ih
