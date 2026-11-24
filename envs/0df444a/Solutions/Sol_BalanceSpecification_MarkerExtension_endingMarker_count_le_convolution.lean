-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.endingMarker_count_le_convolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:25:57.942899+00:00
-- url     : https://prove2.me/submissions/24659a5c-7e1b-4d4d-904b-931f6469186e

module
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix
public import Definitions.Def_BalanceSpecificaton_RenewalBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerWordBounds
public import Theorems.Thm_BalanceSpecification_MarkerExtension_mem_endingMarkerFinset
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_MarkerExtension_marked_ending_marker_normalForm
public import Theorems.Thm_BalanceSpecification_MarkerExtension_mem_payloadSuffixFinset
public import Theorems.Thm_BalanceSpecification_MarkerExtension_mem_payloadSuffixFinset_iff
public import Theorems.Thm_BalanceSpecification_MarkerExtension_word_before_marker_suffix_payload
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
    (endingMarkerFinset (shift M hM x s) (n + 1)).card ≤
      ∑ l ∈ Finset.range (n + 1), (payloadSuffixFinset M hM x s l).card *
        wordCount (generatedWords (code M hM x s)) (n - l) := by
  classical
  let F : ℕ → Finset (Word (Option A)) := fun l =>
    ((payloadSuffixFinset M hM x s l).product
      (wordFinset (generatedWords (code M hM x s)) (n - l))).image
      (fun p => p.1.map some ++ p.2 ++ [none])
  have hsub : endingMarkerFinset (shift M hM x s) (n + 1) ⊆
      (Finset.range (n + 1)).biUnion F := by
    intro w hw
    obtain ⟨hwL, hwlen, z, rfl⟩ := mem_endingMarkerFinset.mp hw
    simp only [List.length_append, List.length_singleton] at hwlen
    obtain ⟨a, c, hpre, hc, hform⟩ := marked_ending_marker_normalForm hwL
    have hlength := congrArg List.length hform
    simp only [List.length_append, List.length_map, List.length_singleton] at hlength
    have hsource : a ∈ payloadSuffixFinset M hM x s a.length := by
      apply (mem_payloadSuffixFinset_iff M hM x s).mpr
      exact ⟨rfl, word_before_marker_suffix_payload M hM x s hpre⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨a.length, Finset.mem_range.mpr (by omega), ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨(a, c), Finset.mem_product.mpr ⟨hsource, ?_⟩, hform.symm⟩
    exact mem_wordFinset.mpr ⟨hc, by
      change c.length = n - a.length
      omega⟩
  calc
    (endingMarkerFinset (shift M hM x s) (n + 1)).card ≤
        ((Finset.range (n + 1)).biUnion F).card := Finset.card_le_card hsub
    _ ≤ ∑ l ∈ Finset.range (n + 1), (F l).card := Finset.card_biUnion_le
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro l _
      exact Finset.card_image_le.trans_eq (Finset.card_product _ _)
end BalanceSpecification.MarkerExtension
