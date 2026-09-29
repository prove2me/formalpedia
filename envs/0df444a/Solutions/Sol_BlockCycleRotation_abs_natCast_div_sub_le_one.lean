-- Prove2me | solution 1 for BlockCycleRotation.abs_natCast_div_sub_le_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:26:41.975274+00:00
-- url     : https://prove2.me/submissions/1d1df8be-1f81-4977-8670-8449bfa707e8

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
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

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

/-- The floor is within `1` from below. -/
theorem lt_natCast_div_add_one {x y : ℕ} (hy : 0 < y) :
    (x : ℝ) / (y : ℝ) < ((x / y : ℕ) : ℝ) + 1 := by
  have hy' : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  rw [div_lt_iff₀ hy']
  have h1 : x < y * (x / y + 1) := by
    have h2 := Nat.div_add_mod x y
    have h3 := Nat.mod_lt x hy
    nlinarith
  have h4 : (x : ℝ) < ((y * (x / y + 1) : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h4
  linarith

end BlockCycleRotation

open BlockCycleRotation in
/-- **The floor is within `1` of the real quotient.** -/
theorem solution {x y : ℕ} (hy : 0 < y) :
    |((x / y : ℕ) : ℝ) - (x : ℝ) / (y : ℝ)| ≤ 1:= by
  have h1 : ((x / y : ℕ) : ℝ) ≤ (x : ℝ) / (y : ℝ) := Nat.cast_div_le
  have h2 : (x : ℝ) / (y : ℝ) < ((x / y : ℕ) : ℝ) + 1 := lt_natCast_div_add_one hy
  rw [abs_le]
  constructor <;> linarith
