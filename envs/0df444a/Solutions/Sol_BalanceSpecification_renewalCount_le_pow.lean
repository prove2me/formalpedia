-- Prove2me | solution 1 for BalanceSpecification.renewalCount_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:01.25597+00:00
-- url     : https://prove2.me/submissions/5f2a8b53-fc4a-4f94-8e6e-1408afc6098b

module
public import Definitions.Def_BalanceSpecificaton_SGap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Theorems.Thm_BalanceSpecification_sGapListConcat_nil
public import Theorems.Thm_BalanceSpecification_sGapListConcat_cons
public import Theorems.Thm_BalanceSpecification_mem_renewalFinset
public import Theorems.Thm_BalanceSpecification_renewalCount_zero
public import Theorems.Thm_BalanceSpecification_mem_renewalGaps
public import Theorems.Thm_BalanceSpecification_renewalCount_recurrence
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.nil_mem_generatedWords
attribute [local simp] BalanceSpecification.periodicConfiguration_shift
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage


attribute [local simp] BalanceSpecification.sGapListConcat_nil
attribute [local simp] BalanceSpecification.sGapListConcat_cons
attribute [local simp] BalanceSpecification.mem_renewalFinset
attribute [local simp] BalanceSpecification.renewalCount_zero
attribute [local simp] BalanceSpecification.mem_renewalGaps

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {S : Set ℕ} {β : ℝ} (hβ : 0 < β)
    (hpressure : ∀ F : Finset ℕ, (∀ s ∈ F, s ∈ S) →
      (∑ s ∈ F, (β⁻¹) ^ (s + 1)) ≤ 1) (n : ℕ) :
    (renewalCount S n : ℝ) ≤ β ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp only [renewalCount_zero, Nat.cast_one, pow_zero, le_refl]
    · have hn' : 0 < n := Nat.pos_of_ne_zero hn
      rw [renewalCount_recurrence S hn', Nat.cast_sum]
      calc
        (∑ s ∈ renewalGaps S n, (renewalCount S (n - s - 1) : ℝ)) ≤
            ∑ s ∈ renewalGaps S n, β ^ (n - s - 1) := by
          apply Finset.sum_le_sum
          intro s hs
          exact ih _ (by omega)
        _ = β ^ n * (∑ s ∈ renewalGaps S n, (β⁻¹) ^ (s + 1)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          have hsn := (mem_renewalGaps.mp hs).1
          rw [inv_pow, ← div_eq_mul_inv]
          apply (eq_div_iff (pow_ne_zero _ hβ.ne')).mpr
          rw [← pow_add]
          congr 1
          omega
        _ ≤ β ^ n * 1 := mul_le_mul_of_nonneg_left
          (hpressure _ (fun s hs => (mem_renewalGaps.mp hs).2)) (pow_nonneg hβ.le n)
        _ = β ^ n := mul_one _
end BalanceSpecification
