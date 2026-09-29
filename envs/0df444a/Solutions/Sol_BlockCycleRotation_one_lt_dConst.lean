-- Prove2me | solution 1 for BlockCycleRotation.one_lt_dConst
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:35:46.690335+00:00
-- url     : https://prove2.me/submissions/6eb98042-79b2-4f5d-96c4-ef7f1e551cec

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_cTerm_row_le
import Theorems.Thm_BlockCycleRotation_cTerm_summable
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

/-- `C` as an iterated sum: first over `a'`, then over `a`. -/
theorem cConst_eq_tsum_rows : cConst = ∑' a : ℕ, ∑' a' : ℕ, cTerm (a, a') :=
  cTerm_summable.tsum_prod

/-- `C` as a sum of finite rows. -/
theorem cConst_eq_tsum_finRows : cConst = ∑' a : ℕ, ∑ a' ∈ Finset.range a, cTerm (a, a') := by
  rw [cConst_eq_tsum_rows]
  refine tsum_congr fun a => ?_
  exact tsum_eq_sum (s := Finset.range a) (cTerm_row_support a)

/-- The row sums are summable. -/
theorem cRow_summable : Summable (fun a : ℕ => ∑ a' ∈ Finset.range a, cTerm (a, a')) := by
  have hg : Summable (fun a : ℕ => 3 / (2 * (a : ℝ) ^ 2)) := by
    have h : Summable (fun a : ℕ => 1 / (a : ℝ) ^ 2) := by
      rw [Real.summable_one_div_nat_pow]
      norm_num
    refine (h.mul_left (3 / 2)).congr fun a => ?_
    rw [div_mul_eq_mul_div, mul_one_div]
    ring_nf
  refine Summable.of_nonneg_of_le (fun a => ?_) cTerm_row_le hg
  exact Finset.sum_nonneg fun a' _ => cTerm_nonneg _

end BlockCycleRotation

open BlockCycleRotation in
/-- `D > 1`, so the constant is not degenerate. -/
theorem solution : 1 < dConst:= by
  rw [dConst]
  have h : 0 < cConst := by
    have h1 : cTerm (2, 1) ≤ ∑ a' ∈ Finset.range 2, cTerm (2, a') := by
      refine Finset.single_le_sum (fun i _ => cTerm_nonneg _) ?_
      simp
    have h2 : (0 : ℝ) < cTerm (2, 1) := by
      unfold cTerm
      rw [if_pos (by norm_num)]
      norm_num
    have h3 : ∑ a' ∈ Finset.range 2, cTerm (2, a') ≤ cConst := by
      rw [cConst_eq_tsum_finRows]
      exact (cRow_summable).le_tsum 2 (fun b _ => Finset.sum_nonneg fun a' _ => cTerm_nonneg _)
    linarith
  linarith
