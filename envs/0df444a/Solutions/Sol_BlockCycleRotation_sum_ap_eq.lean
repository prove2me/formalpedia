-- Prove2me | solution 1 for BlockCycleRotation.sum_ap_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:39:33.678379+00:00
-- url     : https://prove2.me/submissions/755b3f1a-898b-4611-a91c-05525997855a

import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_indicator_eq
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
/-- **The character expansion of a sum over an arithmetic progression.**
The `m = 0` term is the main term; the rest is the error. -/
theorem solution {a : ℕ} (ha : 0 < a) (c : ℤ) (A B : ℂ) (T : ℕ) :
    (∑ b ∈ Finset.Ico 1 T, if (a : ℤ) ∣ ((b : ℤ) - c) then (A + B * b) else 0)
      = (1 / (a : ℂ)) * ((∑ b ∈ Finset.Ico 1 T, (A + B * b))
          + ∑ m ∈ Finset.Ico 1 a, e (-(2 * π * (m : ℝ) * (c : ℝ) / a))
              * ∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b):= by
  have pointwise : ∀ b ∈ Finset.Ico 1 T,
      (if (a : ℤ) ∣ ((b : ℤ) - c) then (A + B * b) else 0)
        = ∑ m ∈ Finset.range a, (1 / (a : ℂ)) * ((A + B * b)
            * (e (2 * π * (m : ℝ) / a) ^ b * e (-(2 * π * (m : ℝ) * (c : ℝ) / a)))) := by
    intro b _
    have hite : (if (a : ℤ) ∣ ((b : ℤ) - c) then (A + B * b) else 0)
        = (A + B * b) * (if (a : ℤ) ∣ ((b : ℤ) - c) then (1 : ℂ) else 0) := by
      by_cases hd : (a : ℤ) ∣ ((b : ℤ) - c) <;> simp [hd]
    rw [hite, indicator_eq ha c b, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [Finset.sum_congr rfl pointwise, Finset.sum_comm]
  have inner : ∀ m : ℕ,
      (∑ b ∈ Finset.Ico 1 T, (1 / (a : ℂ)) * ((A + B * b)
          * (e (2 * π * (m : ℝ) / a) ^ b * e (-(2 * π * (m : ℝ) * (c : ℝ) / a)))))
        = (1 / (a : ℂ)) * (e (-(2 * π * (m : ℝ) * (c : ℝ) / a))
            * ∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b) := by
    intro m
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [Finset.sum_congr rfl (fun m _ => inner m), ← Finset.mul_sum,
    Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot ha]
  congr 2
  · simp [e_zero]
