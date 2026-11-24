-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.exists_source_word_followers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:51.875249+00:00
-- url     : https://prove2.me/submissions/6a6a6c29-b06c-40da-bf7e-676baa53b8c6

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerRight
public import Theorems.Thm_BalanceSpecification_MarkerExtension_exists_last_marker_split
public import Theorems.Thm_BalanceSpecification_IsFactorial_prefix
public import Theorems.Thm_BalanceSpecification_IsFactorial_suffix
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_language_factorial
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
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*}
variable [TopologicalSpace A] [TopologicalSpace (Option A)]
  {Y : ShiftSpace A} {X : ShiftSpace (Option A)}
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution
    (hmarker : IsSynchronizing (language X) [none])
    (hF : ∀ v ∈ language Y, [none] ++ v.map some ∈ language X)
    (hNonMarker : ∀ u ∈ language X, none ∉ u →
      ∃ v ∈ language Y, u = v.map some)
    {u : Word (Option A)} (hu : u ∈ language X) :
    ∃ v ∈ language Y, ∀ w ∈ language Y, v ++ w ∈ language Y →
      u ++ w.map some ∈ language X := by
  by_cases hnone : none ∈ u
  · obtain ⟨p, q, hsplit, hq⟩ := exists_last_marker_split hnone
    have hu' : (p ++ [none]) ++ q ∈ language X := by
      simpa only [hsplit, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using hu
    have hp : p ++ [none] ∈ language X := (language_factorial X).prefix hu'
    have hqL : q ∈ language X := (language_factorial X).suffix hu'
    obtain ⟨v, hv, hqv⟩ := hNonMarker q hqL hq
    refine ⟨v, hv, ?_⟩
    intro w hw hvw
    have hright : [none] ++ (q ++ w.map some) ∈ language X := by
      simpa only [hqv, List.map_append, List.append_assoc] using hF (v ++ w) hvw
    have H := hmarker.2 p (q ++ w.map some) hp hright
    simpa only [hsplit, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using H
  · obtain ⟨v, hv, huv⟩ := hNonMarker u hu hnone
    refine ⟨v, hv, ?_⟩
    intro w hw hvw
    have H := (language_factorial X).suffix (hF (v ++ w) hvw)
    simpa only [huv, List.map_append] using H
end BalanceSpecification.MarkerExtension
