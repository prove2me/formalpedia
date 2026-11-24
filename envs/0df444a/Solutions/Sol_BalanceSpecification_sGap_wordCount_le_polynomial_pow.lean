-- Prove2me | solution 1 for BalanceSpecification.sGap_wordCount_le_polynomial_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:02.186804+00:00
-- url     : https://prove2.me/submissions/9d6862f0-76ca-496c-a619-333cc42a5d1c

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
public import Theorems.Thm_BalanceSpecification_renewalCount_le_pow
public import Theorems.Thm_BalanceSpecification_sGap_wordCount_le_renewal_sum
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
theorem _root_.solution [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) {β : ℝ} (hβ : 1 < β)
    (hpressure : ∀ F : Finset ℕ, (∀ s ∈ F, s ∈ S) →
      (∑ s ∈ F, (β⁻¹) ^ (s + 1)) ≤ 1) (n : ℕ) :
    (wordCount (language (sGapShift S)) n : ℝ) ≤
      2 * ((n : ℝ) + 1)^2 * β^n := by
  have hβpos : 0 < β := lt_trans zero_lt_one hβ
  have hβone : 1 ≤ β^n := one_le_pow₀ hβ.le
  have hrenewal (a m : ℕ) : (renewalCount S (n - a - m - 1) : ℝ) ≤ β^n :=
    (renewalCount_le_pow hβpos hpressure _).trans (pow_le_pow_right₀ hβ.le (by omega))
  have hsum : (∑ a ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
      (renewalCount S (n - a - m - 1) : ℝ)) ≤ (((n : ℝ) + 1)^2) * β^n := by
    calc
      (∑ a ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
          (renewalCount S (n - a - m - 1) : ℝ)) ≤
          ∑ a ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1), β^n := by
        apply Finset.sum_le_sum
        intro a ha
        exact Finset.sum_le_sum (fun m hm => hrenewal a m)
      _ = (((n : ℝ) + 1)^2) * β^n := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        ring
  have hraw : (wordCount (language (sGapShift S)) n : ℝ) ≤
      1 + ∑ a ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
        (renewalCount S (n - a - m - 1) : ℝ) := by
    exact_mod_cast sGap_wordCount_le_renewal_sum hS n
  have hpoly : 1 ≤ ((n : ℝ) + 1)^2 := by
    have hn := Nat.cast_nonneg (α := ℝ) n
    nlinarith only [hn]
  have hterm : 1 ≤ ((n : ℝ) + 1)^2 * β^n := one_le_mul_of_one_le_of_one_le hpoly hβone
  nlinarith only [hraw, hsum, hterm]
end BalanceSpecification
