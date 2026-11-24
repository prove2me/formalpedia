-- Prove2me | solution 1 for BalanceSpecification.wordCount_zero_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:24.120557+00:00
-- url     : https://prove2.me/submissions/4db4d228-1437-4786-a94c-af6a4842cea2

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CountBounds
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



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] {L : Set (Word A)}
namespace BalanceSpecification
theorem _root_.solution (L : Set (Word A)) : wordCount L 0 ≤ 1 := by
  classical
  calc
    wordCount L 0 ≤ ({[]} : Finset (Word A)).card := by
      apply Finset.card_le_card
      intro w hw
      have hwlen := (mem_wordFinset.mp hw).2
      simpa only [List.length_eq_zero_iff.mp hwlen] using Finset.mem_singleton_self ([] : Word A)
    _ = 1 := Finset.card_singleton _
end BalanceSpecification
