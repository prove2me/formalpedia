-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.word_last_marker_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:40.80165+00:00
-- url     : https://prove2.me/submissions/bf0c08ff-2e74-4a0c-a7f8-615cb546505d

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Theorems.Thm_BalanceSpecification_MarkerExtension_split_last_marker
public import Theorems.Thm_BalanceSpecification_MarkerExtension_map_word_mem_language_iff
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
variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]
variable {Y : ShiftSpace A} (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
omit [DiscreteTopology A] [Fintype A]
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution {w : Word (Option A)}
    (hw : w ∈ language (shift M hM x s)) :
    (∃ v ∈ language Y, w = v.map some) ∨
      ∃ u : Word (Option A), ∃ v ∈ language Y,
        u ++ [none] ∈ language (shift M hM x s) ∧ w = (u ++ [none]) ++ v.map some := by
  rcases split_last_marker w with ⟨v, rfl⟩ | ⟨u, v, rfl⟩
  · exact Or.inl ⟨v, (map_word_mem_language_iff M hM x s).mp hw, rfl⟩
  · have hsuffix : v.map some ∈ language (shift M hM x s) :=
      language_factorial (shift M hM x s) ⟨u ++ [none], [], by
        simp only [List.append_nil, List.append_assoc, List.singleton_append]⟩ hw
    have hprefix : u ++ [none] ∈ language (shift M hM x s) :=
      language_factorial (shift M hM x s) ⟨[], v.map some, by
        simp only [List.nil_append, List.append_assoc, List.singleton_append]⟩ hw
    exact Or.inr ⟨u, v, (map_word_mem_language_iff M hM x s).mp hsuffix, hprefix,
      by simp only [List.append_assoc, List.singleton_append]⟩
end BalanceSpecification.MarkerExtension
