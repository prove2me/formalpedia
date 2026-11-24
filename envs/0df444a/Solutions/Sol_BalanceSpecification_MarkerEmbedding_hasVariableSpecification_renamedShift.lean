-- Prove2me | solution 1 for BalanceSpecification.MarkerEmbedding.hasVariableSpecification_renamedShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:33.053457+00:00
-- url     : https://prove2.me/submissions/8ee6559f-a6e2-40eb-b0eb-ef16adaec12c

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_Specification
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_mem_language_renamedShift_iff
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage


attribute [local simp] BalanceSpecification.MarkerEmbedding.block_mapConfiguration

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerEmbedding
variable {A B : Type*}
variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace B] [T2Space B]
namespace BalanceSpecification.MarkerEmbedding
theorem _root_.solution (f : A → B) {Y : ShiftSpace A}
    (hY : HasVariableSpecification Y) : HasVariableSpecification (renamedShift f Y) := by
  obtain ⟨M, hM⟩ := hY
  refine ⟨M, ?_⟩
  intro u hu v hv
  obtain ⟨u', hu', rfl⟩ := (mem_language_renamedShift_iff f).mp hu
  obtain ⟨v', hv', rfl⟩ := (mem_language_renamedShift_iff f).mp hv
  obtain ⟨b, hb, hblen, hconcat⟩ := hM u' hu' v' hv'
  refine ⟨b.map f, (mem_language_renamedShift_iff f).mpr ⟨b, hb, rfl⟩, ?_, ?_⟩
  · simpa only [List.length_map] using hblen
  · apply (mem_language_renamedShift_iff f).mpr
    exact ⟨u' ++ b ++ v', hconcat, by simp only [List.map_append]⟩
end BalanceSpecification.MarkerEmbedding
