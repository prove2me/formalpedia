-- Prove2me | solution 1 for BalanceSpecification.MarkerEmbedding.wordFinset_renamedShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:20:13.468054+00:00
-- url     : https://prove2.me/submissions/e001afff-cd42-482e-ab7f-7a847b35548f

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
open scoped Classical
namespace BalanceSpecification.MarkerEmbedding
theorem _root_.solution [Fintype B] (f : A → B) (Y : ShiftSpace A) (n : ℕ) :
    wordFinset (language (renamedShift f Y)) n =
      (wordFinset (language Y) n).image (List.map f) := by
  classical
  ext w
  simp only [mem_wordFinset, mem_language_renamedShift_iff, Finset.mem_image]
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hlen⟩
    exact ⟨v, ⟨hv, by simpa only [List.length_map] using hlen⟩, rfl⟩
  · rintro ⟨v, ⟨hv, hlen⟩, rfl⟩
    exact ⟨⟨v, hv, rfl⟩, by simpa only [List.length_map] using hlen⟩
end BalanceSpecification.MarkerEmbedding
