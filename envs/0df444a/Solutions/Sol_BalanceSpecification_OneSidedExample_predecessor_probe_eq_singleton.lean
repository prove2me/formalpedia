-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.predecessor_probe_eq_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:58:17.043898+00:00
-- url     : https://prove2.me/submissions/a25bbb65-d0c8-4b8e-b68a-7c6e7463c1bb

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Theorems.Thm_BalanceSpecification_OneSidedExample_predecessor_probe_subset
public import Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_mem_language
public import Theorems.Thm_BalanceSpecification_OneSidedExample_ascending_q_walk
public import Theorems.Thm_BalanceSpecification_OneSidedExample_generator_mem_language
public import Theorems.Thm_BalanceSpecification_OneSidedExample_length_runWord
public import Theorems.Thm_BalanceSpecification_OneSidedExample_paired_mem_code
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
    predecessorFinset (language shift) (probeWord n) n = {List.replicate n a} := by
  apply Finset.Subset.antisymm (predecessor_probe_subset hn)
  intro v hv
  have hv' : v = List.replicate n a := Finset.mem_singleton.mp hv
  rw [hv']
  apply mem_predecessorFinset.mpr
  refine ⟨(ascending_q_walk 0 n).mem_language, List.length_replicate .., ?_⟩
  have hgen := generator_mem_language (paired_mem_code (n := n + 1) (by omega))
  simpa only [probeWord, List.replicate_succ', List.append_assoc,
    List.singleton_append] using hgen
end BalanceSpecification.OneSidedExample
