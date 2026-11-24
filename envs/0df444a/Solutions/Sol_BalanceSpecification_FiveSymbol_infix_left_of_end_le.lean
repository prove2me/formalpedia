-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.infix_left_of_end_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:09:41.328623+00:00
-- url     : https://prove2.me/submissions/7ed4108d-9e5f-454e-8bbc-6447d4c482ce

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
theorem _root_.solution {f u v p q : Word Alphabet}
    (heq : u ++ v = p ++ f ++ q) (hle : p.length + f.length ≤ u.length) : f <:+: u := by
  have hprefix : p ++ f <+: u ++ v := ⟨q, heq.symm⟩
  have hshort : p ++ f <+: u := List.prefix_of_prefix_length_le hprefix
    (List.prefix_append u v) (by simpa only [List.length_append] using hle)
  obtain ⟨t, ht⟩ := hshort
  exact ⟨p, t, ht⟩
end BalanceSpecification.FiveSymbol
