-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.getElem_two_bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:27.014801+00:00
-- url     : https://prove2.me/submissions/f5e52ce6-cca5-4aeb-ad43-964a559de2f0

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
theorem _root_.solution {u v : Word Alphabet} {L t : ℕ}
    (hlo : u.length ≤ t) (hhi : t < u.length + L) :
    (u ++ List.replicate L 2 ++ v)[t]'(by
      simp only [List.length_append, List.length_replicate]; omega) = (2 : Alphabet) := by
  simp only [List.getElem_append_left (show t < (u ++ List.replicate L 2).length by
      simp only [List.length_append, List.length_replicate]; omega),
    List.getElem_append_right hlo, List.getElem_replicate]
end BalanceSpecification.FiveSymbol
