-- Prove2me | solution 1 for BlockCycleRotation.cTerm_summable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:27:36.781041+00:00
-- url     : https://prove2.me/submissions/4a77b510-c516-4155-89eb-14bd76a3643b

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_cTerm_row_le
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

theorem cTerm_nonneg (p : ℕ × ℕ) : 0 ≤ cTerm p := by
  unfold cTerm
  split
  · positivity
  · exact le_refl 0

/-- Each row is supported on `a' < a`. -/
theorem cTerm_row_support (a a' : ℕ) (h : a' ∉ Finset.range a) : cTerm (a, a') = 0 := by
  simp only [Finset.mem_range, not_lt] at h
  unfold cTerm
  rw [if_neg]
  rintro ⟨-, h2, -⟩
  exact absurd h2 (by omega)

theorem cTerm_row_summable (a : ℕ) : Summable (fun a' => cTerm (a, a')) :=
  summable_of_ne_finset_zero (s := Finset.range a) (cTerm_row_support a)

theorem cTerm_row_tsum_le (a : ℕ) : ∑' a', cTerm (a, a') ≤ 3 / (2 * (a : ℝ) ^ 2) := by
  rw [tsum_eq_sum (s := Finset.range a) (cTerm_row_support a)]
  exact cTerm_row_le a

end BlockCycleRotation

open BlockCycleRotation in
/-- **The series for `C` converges.** -/
theorem solution : Summable cTerm:= by
  rw [summable_prod_of_nonneg (fun p => cTerm_nonneg p)]
  refine ⟨cTerm_row_summable, ?_⟩
  have hg : Summable (fun a : ℕ => 3 / (2 * (a : ℝ) ^ 2)) := by
    have h : Summable (fun a : ℕ => 1 / (a : ℝ) ^ 2) := by
      rw [Real.summable_one_div_nat_pow]
      norm_num
    refine (h.mul_left (3 / 2)).congr fun a => ?_
    rw [div_mul_eq_mul_div, mul_one_div]
    ring_nf
  refine Summable.of_nonneg_of_le (fun a => ?_) cTerm_row_tsum_le hg
  exact tsum_nonneg fun a' => cTerm_nonneg _
