-- Prove2me | solution 1 for BlockCycleRotation.cConst_le_partial_add
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:28:58.150837+00:00
-- url     : https://prove2.me/submissions/970f3624-dc83-4da2-aa7d-b51b2db2f4d5

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_cTerm_row_le
import Theorems.Thm_BlockCycleRotation_cTerm_summable
import Theorems.Thm_BlockCycleRotation_sum_inv_sq_tail_le
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

end BlockCycleRotation

open BlockCycleRotation in
/-- **The tail bound for `C`.**  Truncating the series at `a ≤ N` loses at most
`3/(2N)`. -/
theorem solution {N : ℕ} (hN : 0 < N) :
    cConst ≤ (∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a, cTerm (a, a'))
      + 3 / (2 * (N : ℝ)):= by
  rw [cConst_eq_tsum_finRows]
  refine Real.tsum_le_of_sum_le
    (fun a => Finset.sum_nonneg fun a' _ => cTerm_nonneg _) fun s => ?_
  classical
  have hsplit : ∑ a ∈ s, (∑ a' ∈ Finset.range a, cTerm (a, a'))
      = (∑ a ∈ s.filter (fun a => a ≤ N), ∑ a' ∈ Finset.range a, cTerm (a, a'))
        + ∑ a ∈ s.filter (fun a => ¬ a ≤ N), ∑ a' ∈ Finset.range a, cTerm (a, a') :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hlow : (∑ a ∈ s.filter (fun a => a ≤ N), ∑ a' ∈ Finset.range a, cTerm (a, a'))
      ≤ ∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a, cTerm (a, a') := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun a _ _ => Finset.sum_nonneg fun a' _ => cTerm_nonneg _)
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    omega
  have hhigh : (∑ a ∈ s.filter (fun a => ¬ a ≤ N), ∑ a' ∈ Finset.range a, cTerm (a, a'))
      ≤ 3 / (2 * (N : ℝ)) := by
    have h1 : (∑ a ∈ s.filter (fun a => ¬ a ≤ N), ∑ a' ∈ Finset.range a, cTerm (a, a'))
        ≤ ∑ a ∈ s.filter (fun a => ¬ a ≤ N), 3 / (2 * (a : ℝ) ^ 2) :=
      Finset.sum_le_sum fun a _ => cTerm_row_le a
    have h2 : (∑ a ∈ s.filter (fun a => ¬ a ≤ N), 3 / (2 * (a : ℝ) ^ 2))
        = (3 / 2) * ∑ a ∈ s.filter (fun a => ¬ a ≤ N), 1 / ((a : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [div_mul_eq_mul_div, mul_one_div]
      ring_nf
    have h3 : (∑ a ∈ s.filter (fun a => ¬ a ≤ N), 1 / ((a : ℝ) ^ 2)) ≤ 1 / (N : ℝ) := by
      refine sum_inv_sq_tail_le hN _ fun a ha => ?_
      simp only [Finset.mem_filter] at ha
      omega
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [h2] at h1
    have : (3 / 2 : ℝ) * (1 / (N : ℝ)) = 3 / (2 * (N : ℝ)) := by field_simp
    nlinarith [h1, h3]
  rw [hsplit]
  linarith
