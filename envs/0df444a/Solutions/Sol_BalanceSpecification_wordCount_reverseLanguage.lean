-- Prove2me | solution 1 for BalanceSpecification.wordCount_reverseLanguage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:34:44.038097+00:00
-- url     : https://prove2.me/submissions/1d3751d4-1fff-494a-9b01-8156297506d7

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
theorem _root_.solution (L : Set (Word A)) (n : ℕ) :
    wordCount (reverseLanguage L) n = wordCount L n := by
  classical
  unfold wordCount
  refine Finset.card_bij' (fun w _ => w.reverse) (fun w _ => w.reverse) ?_ ?_ ?_ ?_
  · intro w hw
    obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
    exact mem_wordFinset.mpr ⟨hwL, by simpa only [List.length_reverse] using hwlen⟩
  · intro w hw
    obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
    exact mem_wordFinset.mpr ⟨by simpa only [reverseLanguage, Set.mem_ofPred_eq,
      List.reverse_reverse] using hwL, by simpa only [List.length_reverse] using hwlen⟩
  · intro w hw
    exact List.reverse_reverse w
  · intro w hw
    exact List.reverse_reverse w
end BalanceSpecification
