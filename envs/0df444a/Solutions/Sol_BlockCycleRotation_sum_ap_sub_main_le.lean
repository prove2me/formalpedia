-- Prove2me | solution 1 for BlockCycleRotation.sum_ap_sub_main_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:40:34.730405+00:00
-- url     : https://prove2.me/submissions/e8cee539-73d2-4538-a4af-b21a4dddc644

import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_norm_sum_twisted_le
import Theorems.Thm_BlockCycleRotation_sum_ap_eq
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

end BlockCycleRotation

open BlockCycleRotation in
/-- **Sums over an arithmetic progression.**  Replacing the sum by its expected
value costs a harmonic sum, i.e. `O(log a)`. -/
theorem solution {a : ℕ} (ha : 0 < a) (c : ℤ) (A B : ℂ) (T : ℕ) :
    ‖(∑ b ∈ Finset.Ico 1 T, if (a : ℤ) ∣ ((b : ℤ) - c) then (A + B * b) else 0)
        - (1 / (a : ℂ)) * ∑ b ∈ Finset.Ico 1 T, (A + B * b)‖
      ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ):= by
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  have hane : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  rw [sum_ap_eq ha c A B T]
  have hsub : (1 / (a : ℂ)) * ((∑ b ∈ Finset.Ico 1 T, (A + B * b))
        + ∑ m ∈ Finset.Ico 1 a, e (-(2 * π * (m : ℝ) * (c : ℝ) / a))
            * ∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b)
      - (1 / (a : ℂ)) * ∑ b ∈ Finset.Ico 1 T, (A + B * b)
      = (1 / (a : ℂ)) * ∑ m ∈ Finset.Ico 1 a, e (-(2 * π * (m : ℝ) * (c : ℝ) / a))
            * ∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b := by
    ring
  rw [hsub, norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have hbound := norm_sum_twisted_le (a := a) A B T
    (fun m => e (-(2 * π * (m : ℝ) * (c : ℝ) / a))) (fun m => le_of_eq (norm_e _))
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hapos]
  calc ‖∑ m ∈ Finset.Ico 1 a, e (-(2 * π * (m : ℝ) * (c : ℝ) / a))
          * ∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b‖
      ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (a : ℝ)
          * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ) := hbound
    _ = (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ)) * (a : ℝ) := by
        ring
