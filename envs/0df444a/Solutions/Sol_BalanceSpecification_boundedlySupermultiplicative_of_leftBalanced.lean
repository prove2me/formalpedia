-- Prove2me | solution 1 for BalanceSpecification.boundedlySupermultiplicative_of_leftBalanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:51.729743+00:00
-- url     : https://prove2.me/submissions/e7933dfe-f8fb-4acb-823b-f0e8cefd1b50

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Theorems.Thm_BalanceSpecification_boundedlySupermultiplicative_of_rightBalanced
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_rightBalanced_reverseLanguage_of_leftBalanced
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset


attribute [local simp] BalanceSpecification.wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}
namespace BalanceSpecification
theorem _root_.solution (hL : IsFactorial L)
    (h : LeftBalanced L) : BoundedlySupermultiplicative L := by
  obtain ⟨c, hc, hbound⟩ := boundedlySupermultiplicative_of_rightBalanced
    hL.reverseLanguage (rightBalanced_reverseLanguage_of_leftBalanced h)
  refine ⟨c, hc, ?_⟩
  intro m n
  simpa only [wordCount_reverseLanguage] using hbound m n
end BalanceSpecification
