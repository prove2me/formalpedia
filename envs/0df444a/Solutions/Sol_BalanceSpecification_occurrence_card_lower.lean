-- Prove2me | solution 1 for BalanceSpecification.occurrence_card_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:14.905929+00:00
-- url     : https://prove2.me/submissions/b0fc2bbb-8734-4d90-8a6a-fa1998d38f22

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Theorems.Thm_BalanceSpecification_mem_extensionPairs
public import Theorems.Thm_BalanceSpecification_occurrence_card_eq_sum
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage


attribute [local simp] BalanceSpecification.mem_extensionPairs

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}
namespace BalanceSpecification
theorem _root_.solution {u : Word A} {a b : ℕ} {cL cR : ℝ}
    (hcR : 0 ≤ cR)
    (hR : ∀ v ∈ L, cR * (wordCount L b : ℝ) ≤ (followerFinset L v b).card)
    (hP : cL * (wordCount L a : ℝ) ≤ (predecessorFinset L u a).card) :
    cL * cR * (wordCount L a : ℝ) * wordCount L b ≤
      (occurrenceFinset L u a b).card := by
  rw [occurrence_card_eq_sum, Nat.cast_sum]
  calc
    cL * cR * (wordCount L a : ℝ) * wordCount L b =
        (cL * wordCount L a) * (cR * wordCount L b) := by ring
    _ ≤ (predecessorFinset L u a).card * (cR * wordCount L b) :=
      mul_le_mul_of_nonneg_right hP (mul_nonneg hcR (Nat.cast_nonneg _))
    _ = ∑ _p ∈ predecessorFinset L u a, cR * (wordCount L b : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ predecessorFinset L u a, ((followerFinset L (p ++ u) b).card : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hR (p ++ u) (mem_predecessorFinset.mp hp).2.2
end BalanceSpecification
