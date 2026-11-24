-- Prove2me | solution 1 for BalanceSpecification.occurrence_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:14.401739+00:00
-- url     : https://prove2.me/submissions/d782fcd9-ad26-4956-86b3-2f52b0d1ac98

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Theorems.Thm_BalanceSpecification_mem_extensionPairs
public import Theorems.Thm_BalanceSpecification_occurrence_card_eq_sum
public import Theorems.Thm_BalanceSpecification_follower_card_le
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_predecessor_card_le
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
theorem _root_.solution (u : Word A) (a b : ℕ) :
    (occurrenceFinset L u a b).card ≤ wordCount L a * wordCount L b := by
  rw [occurrence_card_eq_sum]
  calc
    ∑ p ∈ predecessorFinset L u a, (followerFinset L (p ++ u) b).card ≤
        ∑ _p ∈ predecessorFinset L u a, wordCount L b :=
      Finset.sum_le_sum (fun p _ => follower_card_le L (p ++ u) b)
    _ = (predecessorFinset L u a).card * wordCount L b := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    _ ≤ wordCount L a * wordCount L b :=
      Nat.mul_le_mul_right _ (predecessor_card_le L u a)
end BalanceSpecification
