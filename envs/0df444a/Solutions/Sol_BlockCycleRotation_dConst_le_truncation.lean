-- Prove2me | solution 1 for BlockCycleRotation.dConst_le_truncation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:38:50.226997+00:00
-- url     : https://prove2.me/submissions/af986e3c-b7f0-4192-b190-e8fc33cbd2f4

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Remark21
import Theorems.Thm_BlockCycleRotation_sum_inv_sq_tail_le
import Theorems.Thm_BlockCycleRotation_cConst_eq_alternative
import Mathlib

open Real Finset Filter Topology

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

theorem zTerm_nonneg (p : ℕ × ℕ) : 0 ≤ zTerm p := by
  unfold zTerm; split
  · positivity
  · exact le_refl 0

theorem eTerm_nonneg (p : ℕ × ℕ) : 0 ≤ eTerm p := by
  unfold eTerm; split
  · positivity
  · exact le_refl 0

theorem zTerm_col_sum_le (a' : ℕ) (s : Finset ℕ) :
    ∑ a ∈ s, zTerm (a, a') ≤ 1 / (a' : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos a' with rfl | ha'
  · simp [zTerm]
  · have ha'R : (0 : ℝ) < (a' : ℝ) := by exact_mod_cast ha'
    have h1 : ∑ a ∈ s, zTerm (a, a')
        = ∑ a ∈ s.filter (fun a => a' < a), (1 / (a' : ℝ)) * (1 / (a : ℝ) ^ 2) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun a _ => ?_
      unfold zTerm
      by_cases h : a' < a
      · rw [if_pos ⟨ha', h⟩, if_pos h]
        field_simp
      · rw [if_neg (by tauto), if_neg h]
    rw [h1, ← Finset.mul_sum]
    have h3 := sum_inv_sq_tail_le ha' (s.filter (fun a => a' < a))
      (fun a ha => (Finset.mem_filter.1 ha).2)
    calc (1 / (a' : ℝ)) * ∑ a ∈ s.filter (fun a => a' < a), 1 / (a : ℝ) ^ 2
        ≤ (1 / (a' : ℝ)) * (1 / (a' : ℝ)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 1 / (a' : ℝ) ^ 2 := by ring

theorem zTerm_col_summable (a' : ℕ) : Summable (fun a => zTerm (a, a')) :=
  summable_of_sum_le (fun a => zTerm_nonneg (a, a')) (zTerm_col_sum_le a')

theorem zTerm_col_tsum_le (a' : ℕ) : ∑' a, zTerm (a, a') ≤ 1 / (a' : ℝ) ^ 2 :=
  Real.tsum_le_of_sum_le (fun a => zTerm_nonneg (a, a')) (zTerm_col_sum_le a')

theorem zTerm_summable : Summable zTerm := by
  refine (Equiv.prodComm ℕ ℕ).summable_iff.1 ?_
  change Summable (fun q : ℕ × ℕ => zTerm (q.2, q.1))
  have hnn : (0 : ℕ × ℕ → ℝ) ≤ fun q => zTerm (q.2, q.1) := fun q => zTerm_nonneg _
  rw [summable_prod_of_nonneg hnn]
  refine ⟨fun a' => zTerm_col_summable a', ?_⟩
  have hg : Summable (fun a' : ℕ => 1 / (a' : ℝ) ^ 2) := by
    rw [Real.summable_one_div_nat_pow]; norm_num
  refine Summable.of_nonneg_of_le (fun a' => ?_) (fun a' => zTerm_col_tsum_le a') hg
  exact tsum_nonneg fun a => zTerm_nonneg _

theorem eTerm_le_zTerm (p : ℕ × ℕ) : eTerm p ≤ zTerm p := by
  unfold eTerm zTerm
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have ha' : (0 : ℝ) < (p.2 : ℝ) := by
      have : 0 < p.2 := by omega
      exact_mod_cast this
    have ha : (0 : ℝ) < (p.1 : ℝ) := by
      have : 0 < p.1 := by omega
      exact_mod_cast this
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [mul_nonneg ha'.le (mul_nonneg ha.le ha'.le),
      mul_nonneg ha'.le (mul_nonneg ha'.le ha'.le)]
  · exact le_refl 0

theorem eTerm_summable : Summable eTerm :=
  zTerm_summable.of_nonneg_of_le eTerm_nonneg eTerm_le_zTerm

theorem uTerm_pos (d : ℕ) : 0 < uTerm d := by
  unfold uTerm; positivity

theorem uTerm_summable : Summable uTerm := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) := by
    rw [Real.summable_one_div_nat_pow]; norm_num
  refine ((summable_nat_add_iff 1).2 h).congr fun d => ?_
  unfold uTerm
  push_cast
  ring

theorem tsum_uTerm : ∑' d, uTerm d = zeta3 := rfl

theorem zeta3_pos : (0 : ℝ) < zeta3 := by
  have h1 : uTerm 0 ≤ ∑' d, uTerm d :=
    uTerm_summable.le_tsum 0 (fun j _ => (uTerm_pos j).le)
  have h2 : (0 : ℝ) < uTerm 0 := uTerm_pos 0
  rw [← tsum_uTerm]
  linarith

/-- **Truncating `S` bounds `C` from above**, the closing observation of
Remark 21: the terms of `S` are nonnegative, so every partial sum is a lower
bound for `S` and hence gives an upper bound for `C`. -/
theorem cConst_le_truncation (s : Finset (ℕ × ℕ)) :
    cConst ≤ 1 / 2 - (∑ p ∈ s, eTerm p) / (2 * zeta3) := by
  have hz : (0 : ℝ) < zeta3 := zeta3_pos
  have hle : ∑ p ∈ s, eTerm p ≤ sConst :=
    eTerm_summable.sum_le_tsum s (fun p _ => eTerm_nonneg p)
  rw [cConst_eq_alternative]
  have hdiv : (∑ p ∈ s, eTerm p) / (2 * zeta3) ≤ sConst / (2 * zeta3) :=
    div_le_div_of_nonneg_right hle (by positivity)
  linarith

end BlockCycleRotation

open BlockCycleRotation in
/-- The same, for `D = 1 + 4C`. -/
theorem solution (s : Finset (ℕ × ℕ)) :
    dConst ≤ 3 - 2 * (∑ p ∈ s, eTerm p) / zeta3:= by
  have h := cConst_le_truncation s
  have hz : (0 : ℝ) < zeta3 := zeta3_pos
  rw [dConst]
  have hrw : 4 * (1 / 2 - (∑ p ∈ s, eTerm p) / (2 * zeta3))
      = 2 - 2 * (∑ p ∈ s, eTerm p) / zeta3 := by
    field_simp
    ring
  nlinarith [h, hrw]
