-- Prove2me | solution 1 for BalanceSpecification.wordCount_le_of_marker_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:50.254054+00:00
-- url     : https://prove2.me/submissions/af7d0704-fed5-47c0-ba0c-87e658ba55cc

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerNonleft
public import Theorems.Thm_BalanceSpecification_IsFactorial_suffix
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_language_factorial
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_extensionPairs
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.MarkerEmbedding.block_mapConfiguration
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_extensionPairs
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
open BalanceSpecification
variable {A : Type*} [Fintype A] [TopologicalSpace A] [TopologicalSpace (Option A)]
namespace BalanceSpecification
theorem _root_.solution {X : ShiftSpace (Option A)} {Y : ShiftSpace A}
    (hext : ∀ v ∈ language Y, none :: v.map some ∈ language X) (n : ℕ) :
    wordCount (language Y) n ≤ wordCount (language X) n := by
  classical
  apply Finset.card_le_card_of_injOn (List.map some)
  · intro v hv
    obtain ⟨hvL, hvlen⟩ := mem_wordFinset.mp hv
    exact mem_wordFinset.mpr
      ⟨(language_factorial X).suffix (u := [none]) (hext _ hvL),
        by simpa only [List.length_map] using hvlen⟩
  · intro u _ v _ h
    exact (List.map_inj_right (fun _ _ h => Option.some.inj h)).mp h
end BalanceSpecification
