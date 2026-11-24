-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.predecessor_probe_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:52:37.616811+00:00
-- url     : https://prove2.me/submissions/3b72a423-c012-4217-887f-1bc549e1660f

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_eq_replicate_a_of_end_q
public import Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_start_of_probe
public import Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_split
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
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) :
    predecessorFinset (language shift) (probeWord n) n ⊆ {List.replicate n a} := by
  intro v hv
  obtain ⟨_, hvlen, hvprobe⟩ := mem_predecessorFinset.mp hv
  obtain ⟨s, t, hwalk⟩ := mem_language_shift_iff_exists_walk.mp hvprobe
  obtain ⟨z, hvpath, hprobe⟩ := hwalk.split
  obtain ⟨k, rfl, hnk⟩ := hprobe.start_of_probe hn
  have heq := hvpath.eq_replicate_a_of_end_q (by omega)
  exact Finset.mem_singleton.mpr (by simpa only [hvlen] using heq)
end BalanceSpecification.OneSidedExample
