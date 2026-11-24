-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.forbiddenWord_get_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:51:46.045054+00:00
-- url     : https://prove2.me/submissions/bd42ba4a-7df7-4386-8ebc-383f9c81d326

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
    (forbiddenWord j)[(forbiddenWord j).length - 1]'(by
      have := forbiddenWord_length_pos j; omega) = 4 := by
  let q := markerLeft j ++ shortlexWord (A := Alphabet) j ++ [3] ++
    List.replicate (markerLength j) 1
  have heq : forbiddenWord j = q ++ [4] := by
    simp only [forbiddenWord, markerRight, q, List.append_assoc]
  have hlast : (q ++ [4])[q.length]'(by
      simp only [List.length_append, List.length_singleton]; omega) = (4 : Alphabet) := by
    simp only [List.getElem_append_right (Nat.le_refl q.length), Nat.sub_self,
      List.getElem_cons_zero]
  simpa only [heq, List.length_append, List.length_singleton, Nat.add_sub_cancel] using hlast
end BalanceSpecification.FiveSymbol
