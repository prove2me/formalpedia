-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.word_before_marker_suffix_payload
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:23:56.359802+00:00
-- url     : https://prove2.me/submissions/912ceb03-40ca-4fbf-a22e-0739a9dcab5d

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Theorems.Thm_BalanceSpecification_MarkerExtension_none_not_mem_map_some
public import Theorems.Thm_BalanceSpecification_MarkerExtension_marked_generated_cut
public import Theorems.Thm_BalanceSpecification_MarkerExtension_marked_generated_suffix
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_language_codedShift_infix_generatedWords
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
theorem _root_.solution {v : Word A}
    (hv : v.map some ++ [none] ∈ language (shift M hM x s)) :
    ∃ u : PositiveLanguage Y, v <:+ sourcePayload M hM x s u := by
  obtain ⟨z, hz, a, b, heq⟩ := language_codedShift_infix_generatedWords hv
  have heq' : z = (a ++ v.map some) ++ none :: b := by
    rw [← heq]
    simp only [List.append_assoc, List.singleton_append]
  have hpre := (marked_generated_cut hz heq').1
  have hP : (Set.range (sourcePayload M hM x s)).Nonempty := by
    obtain ⟨u⟩ := positiveLanguage_nonempty x
    exact ⟨_, u, rfl⟩
  obtain ⟨p, ⟨u, rfl⟩, hsuffix⟩ := marked_generated_suffix hP hpre
    (none_not_mem_map_some v) (List.suffix_append a (v.map some))
  obtain ⟨q, hq, heq⟩ := List.suffix_map_iff.mp hsuffix
  have hvq : v = q := (List.map_inj_right (fun _ _ h => Option.some.inj h)).mp heq
  exact ⟨u, hvq ▸ hq⟩
end BalanceSpecification.MarkerExtension
