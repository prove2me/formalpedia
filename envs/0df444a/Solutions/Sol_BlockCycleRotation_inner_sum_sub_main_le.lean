-- Prove2me | solution 1 for BlockCycleRotation.inner_sum_sub_main_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:09:14.481551+00:00
-- url     : https://prove2.me/submissions/3543e18d-dcfd-4cbc-a51f-1db46a1c4057

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_sum_ap_sub_main_le
import Theorems.Thm_BlockCycleRotation_sum_inv_le_one_add_log
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

/-- **Sums over an arithmetic progression, with an explicit logarithm.**

Replacing the sum by its expected value costs `O(log a)`. -/
theorem sum_ap_sub_main_le_log {a : ℕ} (ha : 0 < a) (c : ℤ) (A B : ℂ) (T : ℕ) :
    ‖(∑ b ∈ Finset.Ico 1 T, if (a : ℤ) ∣ ((b : ℤ) - c) then (A + B * b) else 0)
        - (1 / (a : ℂ)) * ∑ b ∈ Finset.Ico 1 T, (A + B * b)‖
      ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (1 + Real.log a) := by
  refine (sum_ap_sub_main_le ha c A B T).trans ?_
  have hK : (0 : ℝ) ≤ ‖A‖ + ‖B‖ * (T - 1 : ℕ) := by positivity
  exact mul_le_mul_of_nonneg_left (sum_inv_le_one_add_log a) hK

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **The inner sum of the triple sum.**

For fixed `d`, `a`, `a'`, summing the paper's linear function over an
arithmetic progression modulo `a` differs from its expected value by
`O(log a)`.  This is `sum_ap_sub_main_le_log` at the paper's coefficients. -/
theorem solution (n d a a' : ℕ) (ha : 0 < a) (c : ℤ) (U : ℕ) :
    ‖(∑ b ∈ Finset.Ico 1 U, if (a : ℤ) ∣ ((b : ℤ) - c) then
          (((n : ℂ) / (d * a) + d * a) + (-(a' : ℂ) / a) * b) else 0)
        - (1 / (a : ℂ)) * ∑ b ∈ Finset.Ico 1 U,
            (((n : ℂ) / (d * a) + d * a) + (-(a' : ℂ) / a) * b)‖
      ≤ (‖((n : ℂ) / (d * a) + d * a)‖ + ‖(-(a' : ℂ) / a)‖ * (U - 1 : ℕ))
          * (1 + Real.log a):=
  sum_ap_sub_main_le_log ha c _ _ U
