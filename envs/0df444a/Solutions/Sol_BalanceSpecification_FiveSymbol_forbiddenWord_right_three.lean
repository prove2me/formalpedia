-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.forbiddenWord_right_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:10:01.946809+00:00
-- url     : https://prove2.me/submissions/5fddd0c2-905f-4cac-bbb2-998f039da2ee

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_shortlexWord_zero
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.shortlexWord_zero



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution (j : ℕ) :
    (forbiddenWord j)[rightOffset j]'(by rw [forbiddenWord_length_rightOffset]; omega) = 3 := by
  have hget : ((markerLeft j ++ shortlexWord j) ++ markerRight j)[(markerLeft j ++ shortlexWord (A := Alphabet) j).length]'(by
        simp only [List.length_append, length_markerRight]; omega) = 3 := by
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
      markerRight, List.cons_append, List.nil_append, List.getElem_cons_zero]
  simpa only [forbiddenWord, rightOffset, List.length_append] using hget
end BalanceSpecification.FiveSymbol
