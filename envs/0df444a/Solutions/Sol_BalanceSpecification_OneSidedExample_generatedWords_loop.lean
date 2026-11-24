-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.generatedWords_loop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:04.213809+00:00
-- url     : https://prove2.me/submissions/003234c6-5e00-4878-a65d-cfd999fcec2f

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraph
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Theorems.Thm_BalanceSpecification_OneSidedExample_codeword_loop
public import Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_append
public import Theorems.Thm_BalanceSpecification_OneSidedExample_length_runWord
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
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
theorem _root_.solution {w : Word Alphabet} (hw : w ∈ generatedWords code) :
    Walk (.p 0) w (.p 0) := by
  obtain ⟨ws, hws, rfl⟩ := hw
  induction ws with
  | nil => exact .nil _
  | cons v vs ih =>
    have hv : v ∈ code := hws v (by simp only [List.mem_cons, true_or])
    have hvs : ∀ z ∈ vs, z ∈ code := fun z hz => hws z (List.mem_cons_of_mem v hz)
    exact (codeword_loop hv).append (ih hvs)
end BalanceSpecification.OneSidedExample
