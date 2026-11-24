-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.forbiddenWord_left_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:09:59.974068+00:00
-- url     : https://prove2.me/submissions/38d931d1-3a5a-4aff-b0ba-e938be57c4b0

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
theorem _root_.solution (j : ℕ) {i : ℕ} (hi : i < markerLength j) :
    (forbiddenWord j)[i + 1]'(by rw [length_forbiddenWord]; omega) = 1 := by
  have heq : forbiddenWord j = 0 :: (List.replicate (markerLength j) 1 ++
      ([2] ++ shortlexWord j ++ markerRight j)) := by
    simp only [forbiddenWord, markerLeft, List.append_assoc, List.cons_append, List.nil_append]
  simp only [heq, List.getElem_cons_succ]
  rw [List.getElem_append_left (as := List.replicate (markerLength j) (1 : Alphabet))
    (by simpa only [List.length_replicate] using hi)]
  exact List.getElem_replicate _
end BalanceSpecification.FiveSymbol
