-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.sourceCodeFinsetAt_mem_code_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:26:13.482474+00:00
-- url     : https://prove2.me/submissions/940d4258-7e98-4a2a-a326-ff564ad4f8d9

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_MarkerEstimates
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerCodeCounts
public import Theorems.Thm_BalanceSpecification_MarkerExtension_mem_sourceCodeFinsetAt
public import Theorems.Thm_BalanceSpecification_MarkerExtension_sourceCodeFinsetAt_zero
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_MarkerExtension_sourcePayload_length_of_large
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


attribute [local simp] BalanceSpecification.MarkerExtension.sourceCodeFinsetAt_zero

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
open scoped Classical
variable {A : Type*} [TopologicalSpace A] [Fintype A] {Y : ShiftSpace A}
variable (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution
    (hs : ∀ n : ℕ, 1 ≤ n → n + M ≤ s n)
    {n : ℕ} {z : Word (Option A)} (hz : z ∈ sourceCodeFinsetAt M hM x s n) :
    1 ≤ n ∧ z ∈ code M hM x s ∧ z.length = s n + 1 := by
  obtain ⟨u, hulen, rfl⟩ := (mem_sourceCodeFinsetAt M hM x s).mp hz
  refine ⟨by have := u.property.2; omega,
    ⟨sourcePayload M hM x s u, ⟨u, rfl⟩, rfl⟩, ?_⟩
  simp only [List.length_cons, List.length_map,
    sourcePayload_length_of_large M hM x s hs, hulen]
end BalanceSpecification.MarkerExtension
