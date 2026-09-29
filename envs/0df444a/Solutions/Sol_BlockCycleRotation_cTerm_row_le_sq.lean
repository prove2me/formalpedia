-- Prove2me | solution 1 for BlockCycleRotation.cTerm_row_le_sq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:35:05.557462+00:00
-- url     : https://prove2.me/submissions/0c335573-a09b-453c-9d7f-491fd89f8483

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_cTerm_le_cube
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

end BlockCycleRotation

open BlockCycleRotation in
/-- Each row is at most `1/a²`. -/
theorem solution (a : ℕ) :
    ∑ a' ∈ Finset.range a, cTerm (a, a') ≤ 1 / (a : ℝ) ^ 2:= by
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · subst h0
    simp
  · have ha : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h0
    calc ∑ a' ∈ Finset.range a, cTerm (a, a')
        ≤ ∑ _a' ∈ Finset.range a, 1 / (a : ℝ) ^ 3 :=
          Finset.sum_le_sum fun a' _ => cTerm_le_cube (a, a')
      _ = (a : ℝ) * (1 / (a : ℝ) ^ 3) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = 1 / (a : ℝ) ^ 2 := by
          field_simp
