-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.mem_payloadSuffixFinset_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:24:49.957817+00:00
-- url     : https://prove2.me/submissions/f92e5efd-11ed-49f1-8bd6-67e2bda708e0

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix
public import Theorems.Thm_BalanceSpecification_MarkerExtension_mem_payloadSuffixFinset
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_MarkerExtension_sourcePayload_mem_language
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


attribute [local simp] BalanceSpecification.MarkerExtension.mem_payloadSuffixFinset

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [TopologicalSpace A] {Y : ShiftSpace A}
variable (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
variable [Fintype A]
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution {l : ℕ} {z : Word A} :
    z ∈ payloadSuffixFinset M hM x s l ↔
      z.length = l ∧ ∃ u : PositiveLanguage Y, z <:+ sourcePayload M hM x s u := by
  constructor
  · intro hz
    exact ((mem_payloadSuffixFinset M hM x s).mp hz).2
  · rintro ⟨hzlen, u, hzu⟩
    exact (mem_payloadSuffixFinset M hM x s).mpr
      ⟨language_factorial Y hzu.isInfix (sourcePayload_mem_language M hM x s u),
        hzlen, u, hzu⟩
end BalanceSpecification.MarkerExtension
