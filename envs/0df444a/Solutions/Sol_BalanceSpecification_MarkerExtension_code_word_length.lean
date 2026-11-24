-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.code_word_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:42.256686+00:00
-- url     : https://prove2.me/submissions/e273afdf-58c8-4c6c-bb90-a2303919be91

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Theorems.Thm_BalanceSpecification_MarkerExtension_sourcePayload_length_of_large
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
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
omit [DiscreteTopology A] [Fintype A] [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution (hs : ∀ n : ℕ, 1 ≤ n → n + M ≤ s n)
    {z : Word (Option A)} (hz : z ∈ code M hM x s) :
    ∃ n : ℕ, 1 ≤ n ∧ z.length = s n + 1 := by
  obtain ⟨v, ⟨u, rfl⟩, rfl⟩ := hz
  refine ⟨u.val.length, by have := u.property.2; omega, ?_⟩
  simp only [List.length_cons, List.length_map, sourcePayload_length_of_large M hM x s hs]
end BalanceSpecification.MarkerExtension
