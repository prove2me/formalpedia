-- Prove2me | solution 1 for BalanceSpecification.MarkerEmbedding.mem_language_renamedShift_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:38:58.930977+00:00
-- url     : https://prove2.me/submissions/ab105ab4-ace7-4a60-ae94-981954c8ce34

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_Specification
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_block_mem_language
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
theorem _root_.solution (f : A → B) {Y : ShiftSpace A} {w : Word B} :
    w ∈ language (renamedShift f Y) ↔ ∃ v ∈ language Y, v.map f = w := by
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, k, hblock⟩
    refine ⟨block x k w.length, block_mem_language hx k w.length, ?_⟩
    simpa only [block_mapConfiguration] using hblock
  · rintro ⟨v, ⟨x, hx, k, hblock⟩, rfl⟩
    refine ⟨mapConfiguration f x, ⟨x, hx, rfl⟩, k, ?_⟩
    rw [List.length_map, block_mapConfiguration, hblock]
end BalanceSpecification.MarkerEmbedding
