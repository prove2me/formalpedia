-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.wordCount_le_lastMarker_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:38.083254+00:00
-- url     : https://prove2.me/submissions/5cdc6ff6-dad8-4799-93f4-a16a9e82e129

module
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix
public import Definitions.Def_BalanceSpecificaton_RenewalBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerWordBounds
public import Theorems.Thm_BalanceSpecification_MarkerExtension_mem_endingMarkerFinset
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_MarkerExtension_mem_payloadSuffixFinset
public import Theorems.Thm_BalanceSpecification_MarkerExtension_word_last_marker_cases
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
attribute [local simp] BalanceSpecification.MarkerEmbedding.block_mapConfiguration
attribute [local simp] BalanceSpecification.MarkerExtension.mem_payloadSuffixFinset
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


attribute [local simp] BalanceSpecification.MarkerExtension.mem_endingMarkerFinset

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]
variable {Y : ShiftSpace A} (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
omit [DiscreteTopology A]
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution (n : ℕ) :
    wordCount (language (shift M hM x s)) n ≤ wordCount (language Y) n +
      ∑ k ∈ Finset.range n, (endingMarkerFinset (shift M hM x s) (k + 1)).card *
        wordCount (language Y) (n - (k + 1)) := by
  classical
  let F : ℕ → Finset (Word (Option A)) := fun k =>
    ((endingMarkerFinset (shift M hM x s) (k + 1)).product
      (wordFinset (language Y) (n - (k + 1)))).image (fun p => p.1 ++ p.2.map some)
  have hsub : wordFinset (language (shift M hM x s)) n ⊆
      (wordFinset (language Y) n).image (List.map some) ∪ (Finset.range n).biUnion F := by
    intro w hw
    obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
    rcases word_last_marker_cases M hM x s hwL with ⟨v, hv, rfl⟩ |
      ⟨u, v, hv, hu, rfl⟩
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨v, mem_wordFinset.mpr
        ⟨hv, by simpa only [List.length_map] using hwlen⟩, rfl⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨u.length, Finset.mem_range.mpr (by
        simp only [List.length_append, List.length_singleton, List.length_map] at hwlen
        omega), ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨(u ++ [none], v), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
      · exact mem_endingMarkerFinset.mpr ⟨hu, by simp only [List.length_append, List.length_singleton], u, rfl⟩
      · exact mem_wordFinset.mpr ⟨hv, by
          change v.length = n - (u.length + 1)
          simp only [List.length_append, List.length_singleton, List.length_map] at hwlen
          omega⟩
  calc
    wordCount (language (shift M hM x s)) n ≤
        ((wordFinset (language Y) n).image (List.map some) ∪
          (Finset.range n).biUnion F).card := Finset.card_le_card hsub
    _ ≤ ((wordFinset (language Y) n).image (List.map some)).card +
        ((Finset.range n).biUnion F).card := Finset.card_union_le _ _
    _ ≤ wordCount (language Y) n + ∑ k ∈ Finset.range n, (F k).card :=
      Nat.add_le_add Finset.card_image_le Finset.card_biUnion_le
    _ ≤ _ := by
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro k _
      exact Finset.card_image_le.trans_eq (Finset.card_product _ _)
end BalanceSpecification.MarkerExtension
