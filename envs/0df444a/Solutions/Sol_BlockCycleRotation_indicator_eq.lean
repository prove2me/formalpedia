-- Prove2me | solution 1 for BlockCycleRotation.indicator_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:38:32.41308+00:00
-- url     : https://prove2.me/submissions/6cfb0e8e-368d-46be-8bc4-cd381e1487f8

import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_sum_e_root
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

/-- `e` turns multiplication by a natural number into a power. -/
theorem e_pow (θ : ℝ) (n : ℕ) : e θ ^ n = e (n * θ) := by
  rw [e, e, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `e` turns addition into multiplication. -/
theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  rw [e, e, e, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end BlockCycleRotation

open BlockCycleRotation in
/-- The character expansion of the indicator of `b ≡ c mod a`. -/
theorem solution {a : ℕ} (ha : 0 < a) (c : ℤ) (b : ℕ) :
    (if (a : ℤ) ∣ ((b : ℤ) - c) then (1 : ℂ) else 0)
      = (1 / (a : ℂ)) * ∑ m ∈ Finset.range a,
          e (2 * π * (m : ℝ) / a) ^ b * e (-(2 * π * (m : ℝ) * (c : ℝ) / a)):= by
  have hane : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  have hkey := sum_e_root ha ((b : ℤ) - c)
  have hterm : ∀ m ∈ Finset.range a,
      (e (2 * π * (((b : ℤ) - c : ℤ) : ℝ) / a)) ^ m
        = e (2 * π * (m : ℝ) / a) ^ b * e (-(2 * π * (m : ℝ) * (c : ℝ) / a)) := by
    intro m _
    rw [e_pow, e_pow, ← e_add]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm] at hkey
  rw [hkey]
  by_cases hd : (a : ℤ) ∣ ((b : ℤ) - c)
  · rw [if_pos hd, if_pos hd]
    field_simp
  · rw [if_neg hd, if_neg hd]
    simp
