-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.getElem_infix_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:51:46.548806+00:00
-- url     : https://prove2.me/submissions/7739e96a-e179-4c95-be8b-a16de4ec3e07

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
theorem _root_.solution {f W p q : Word Alphabet}
    (heq : W = p ++ f ++ q) {i : ℕ} (hi : i < f.length) :
    W[p.length + i]'(by
      have H := congrArg List.length heq
      simp only [List.length_append] at H
      omega) = f[i] := by
  have he := List.getElem_of_eq heq
    (show p.length + i < W.length by
      have H := congrArg List.length heq
      simp only [List.length_append] at H
      omega)
  simp only [List.getElem_append_left (show p.length + i < (p ++ f).length by
      simp only [List.length_append]; omega),
    List.getElem_append_right (Nat.le_add_right p.length i), Nat.add_sub_cancel_left] at he
  exact he
end BalanceSpecification.FiveSymbol
