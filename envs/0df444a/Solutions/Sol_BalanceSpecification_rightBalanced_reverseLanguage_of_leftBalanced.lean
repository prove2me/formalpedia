-- Prove2me | solution 1 for BalanceSpecification.rightBalanced_reverseLanguage_of_leftBalanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:50:31.700681+00:00
-- url     : https://prove2.me/submissions/60739606-9d18-4603-bf97-01baac89150a

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
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
theorem _root_.solution (h : LeftBalanced L) :
    RightBalanced (reverseLanguage L) := by
  obtain ⟨c, hc, hbound⟩ := h
  refine ⟨c, hc, ?_⟩
  intro u hu n hn
  simpa only [follower_card_reverseLanguage, wordCount_reverseLanguage] using
    hbound u.reverse hu n hn
end BalanceSpecification
