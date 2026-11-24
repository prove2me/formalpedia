-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.Walk.mem_language
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:38.815843+00:00
-- url     : https://prove2.me/submissions/7beef7ba-7533-4f34-b66f-c1c737301278

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraph
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_loop_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_OneSidedExample_exists_walk_from_base
public import Theorems.Thm_BalanceSpecification_OneSidedExample_exists_walk_to_base
public import Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_append
public import Theorems.Thm_BalanceSpecification_OneSidedExample_c_mem_code
public import Theorems.Thm_BalanceSpecification_OneSidedExample_length_runWord
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_language_codedShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.OneSidedExample.length_runWord
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.nil_mem_generatedWords
attribute [local simp] BalanceSpecification.periodicConfiguration_shift
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
namespace Walk
theorem _root_.solution {s t : Vertex} {w : Word Alphabet} (h : Walk s w t) :
    w ∈ language shift := by
  obtain ⟨p, hp⟩ := exists_walk_from_base s
  obtain ⟨q, hq⟩ := exists_walk_to_base t
  apply (mem_language_codedShift_iff (C := code) ⟨[c], c_mem_code, by simp⟩).mpr
  exact ⟨p ++ w ++ q, (hp.append h |>.append hq).loop_mem_generatedWords, p, q, rfl⟩
end Walk
end BalanceSpecification.OneSidedExample
