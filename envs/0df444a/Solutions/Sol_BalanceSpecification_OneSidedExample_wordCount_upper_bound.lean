-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.wordCount_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:55:42.99367+00:00
-- url     : https://prove2.me/submissions/84d40003-7f81-4980-9728-e14a9f11a8c9

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_mem_positiveWordCover
public import Theorems.Thm_BalanceSpecification_OneSidedExample_positiveWordCover_card_le
public import Theorems.Thm_BalanceSpecification_OneSidedExample_length_runWord
public import Theorems.Thm_BalanceSpecification_OneSidedExample_mem_language_shift_iff_exists_walk
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
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution (n : ℕ) :
    wordCount (language shift) (n + 1) ≤ 5 * 2 ^ n := by
  have hsub : wordFinset (language shift) (n + 1) ⊆ positiveWordCover n := by
    intro w hw
    obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
    obtain ⟨s, t, hwalk⟩ := mem_language_shift_iff_exists_walk.mp hwL
    cases w with
    | nil => simp only [List.length_nil] at hwlen; omega
    | cons d w =>
      have hwlen' : w.length = n := by simp only [List.length_cons] at hwlen; omega
      simpa only [hwlen'] using hwalk.mem_positiveWordCover
  exact (Finset.card_le_card hsub).trans (positiveWordCover_card_le n)
end BalanceSpecification.OneSidedExample
