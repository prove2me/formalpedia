-- Prove2me | solution 1 for BlockCycleRotation.sum_ap_sub_main_le_log_real
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:18:31.802315+00:00
-- url     : https://prove2.me/submissions/dea9eae2-0452-42e9-83de-7109bb83661b

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
/-- The progression estimate, over `ℝ`. -/
theorem solution {a : ℕ} (ha : 0 < a) (c : ℤ) (A B : ℝ) (T : ℕ) :
    |(∑ b ∈ Finset.Ico 1 T, if (a : ℤ) ∣ ((b : ℤ) - c) then (A + B * b) else 0)
        - (1 / (a : ℝ)) * ∑ b ∈ Finset.Ico 1 T, (A + B * b)|
      ≤ (|A| + |B| * (T - 1 : ℕ)) * (1 + Real.log a):= by
  have h := sum_ap_sub_main_le_log ha c (A : ℂ) (B : ℂ) T
  have key : ((((∑ b ∈ Finset.Ico 1 T, if (a : ℤ) ∣ ((b : ℤ) - c) then (A + B * b) else 0)
        - (1 / (a : ℝ)) * ∑ b ∈ Finset.Ico 1 T, (A + B * b) : ℝ)) : ℂ)
      = (∑ b ∈ Finset.Ico 1 T, if (a : ℤ) ∣ ((b : ℤ) - c) then ((A : ℂ) + B * b) else 0)
        - (1 / (a : ℂ)) * ∑ b ∈ Finset.Ico 1 T, ((A : ℂ) + B * b) := by
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    split <;> push_cast <;> ring
  rw [← key, Complex.norm_real] at h
  simpa using h
