-- Prove2me | solution 1 for BalanceSpecification.FiniteEntropy.event_log_inverse_le_divergence_add_log_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:12:58.982815+00:00
-- url     : https://prove2.me/submissions/26b091c4-705e-4661-a681-c88819f55ac4

module
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_AbsoluteContinuity
public import Theorems.Thm_BalanceSpecification_FiniteEntropy_divergence_eq_neg_shannon_sub
public import Theorems.Thm_BalanceSpecification_FiniteEntropy_sub_le_mul_log_div
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiniteEntropy
variable {ι : Type*} [Fintype ι]
namespace BalanceSpecification.FiniteEntropy
theorem _root_.solution
    {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1)
    (S : Finset ι) (hQ : 0 < ∑ i ∈ S, q i) :
    (∑ i ∈ S, p i) * Real.log (1 / (∑ i ∈ S, q i)) ≤
      divergence p q + Real.log 2 := by
  classical
  let Q : ℝ := ∑ i ∈ S, q i
  let r : ι → ℝ := fun i => if i ∈ S then q i / (2 * Q) else q i / 2
  have hr i : 0 < r i := by
    dsimp only [r]
    split
    · exact div_pos (hq i) (mul_pos (by norm_num) hQ)
    · exact div_pos (hq i) (by norm_num)
  have hsumr : ∑ i, r i ≤ 1 := by
    calc
      ∑ i, r i ≤ ∑ i, (q i / 2 + (if i ∈ S then q i / (2 * Q) else 0)) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i ∈ S
        · simp only [r, hi, ite_true]
          linarith only [(div_pos (hq i) (by norm_num : (0 : ℝ) < 2)).le]
        · simp only [r, hi, ite_false, add_zero, le_refl]
      _ = 1 / 2 + Q / (2 * Q) := by
        rw [Finset.sum_add_distrib, Fintype.sum_ite_mem, ← Finset.sum_div,
          ← Finset.sum_div, hqsum]
      _ = 1 := by
        have hQ0 : Q ≠ 0 := hQ.ne'
        field_simp [hQ0]
        ring
  have hD : 0 ≤ divergence p r := by
    have H := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => sub_le_mul_log_div (hp i) (hr i).le (fun _ => hr i))
    simp only [Finset.sum_sub_distrib, hpsum] at H
    change 1 - ∑ i, r i ≤ divergence p r at H
    linarith only [H, hsumr]
  have hlog i : Real.log (r i) = Real.log (q i) - Real.log 2 -
      (if i ∈ S then Real.log Q else 0) := by
    by_cases hi : i ∈ S
    · simp only [r, hi, ite_true]
      rw [Real.log_div (hq i).ne' (mul_pos (by norm_num : (0 : ℝ) < 2) hQ).ne',
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hQ.ne']
      ring
    · simp only [r, hi, ite_false, sub_zero]
      exact Real.log_div (hq i).ne' (by norm_num)
  have hinds : ∑ i, p i * (if i ∈ S then Real.log Q else 0) =
      (∑ i ∈ S, p i) * Real.log Q := by
    simp only [mul_ite, mul_zero, Fintype.sum_ite_mem, Finset.sum_mul]
  have hcross : ∑ i, p i * Real.log (r i) =
      (∑ i, p i * Real.log (q i)) - Real.log 2 - (∑ i ∈ S, p i) * Real.log Q := by
    simp_rw [hlog, mul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hpsum,
      one_mul, hinds]
  rw [divergence_eq_neg_shannon_sub hr, hcross] at hD
  rw [divergence_eq_neg_shannon_sub hq]
  simp only [one_div, Real.log_inv]
  change (∑ i ∈ S, p i) * -Real.log Q ≤ _
  linarith only [hD]
end BalanceSpecification.FiniteEntropy
