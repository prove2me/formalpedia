-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.exists_source_follower_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:59.018646+00:00
-- url     : https://prove2.me/submissions/ad11de58-e2af-4463-9ff7-da8486ef4e88

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerRight
public import Theorems.Thm_BalanceSpecification_MarkerExtension_exists_source_word_followers
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
variable [Fintype A]
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution
    (hmarker : IsSynchronizing (language X) [none])
    (hF : ∀ v ∈ language Y, [none] ++ v.map some ∈ language X)
    (hNonMarker : ∀ u ∈ language X, none ∉ u →
      ∃ v ∈ language Y, u = v.map some)
    {u : Word (Option A)} (hu : u ∈ language X) :
    ∃ v ∈ language Y, ∀ n : ℕ,
      (followerFinset (language Y) v n).card ≤
        (followerFinset (language X) u n).card := by
  classical
  obtain ⟨v, hv, hfollowers⟩ := exists_source_word_followers hmarker hF hNonMarker hu
  refine ⟨v, hv, ?_⟩
  intro n
  apply Finset.card_le_card_of_injOn (fun w : Word A => w.map some)
  · intro w hw
    obtain ⟨hwL, hwlen, hvw⟩ := mem_followerFinset.mp hw
    apply mem_followerFinset.mpr
    exact ⟨(language_factorial X).suffix (hF w hwL),
      by simpa only [List.length_map] using hwlen, hfollowers w hwL hvw⟩
  · intro w hw z hz hmap
    exact (List.map_inj_right (Option.some_injective A)).mp hmap
end BalanceSpecification.MarkerExtension
