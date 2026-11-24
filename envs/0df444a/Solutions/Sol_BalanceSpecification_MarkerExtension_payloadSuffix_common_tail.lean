-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.payloadSuffix_common_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:26:36.078695+00:00
-- url     : https://prove2.me/submissions/22605a9b-9e8d-4f27-9974-b71d1d4dc0c4

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix
public import Theorems.Thm_BalanceSpecification_MarkerExtension_sourceTail_suffix_of_payload_suffix
public import Theorems.Thm_BalanceSpecification_MarkerExtension_mem_payloadSuffixFinset
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
theorem _root_.solution
    (hs : ∀ n : ℕ, 1 ≤ n → n + M ≤ s n)
    (hb : Monotone (suffixLength M s)) {l m : ℕ}
    (hmin : ∀ n : ℕ, 1 ≤ n → l ≤ s n → m ≤ n)
    {z : Word A} (hz : z ∈ payloadSuffixFinset M hM x s l) :
    sourceTail x (min l (suffixLength M s m)) <:+ z := by
  obtain ⟨_, hzlen, u, hzu⟩ := (mem_payloadSuffixFinset M hM x s).mp hz
  have hun : 1 ≤ u.val.length := u.property.2
  have hlen : l ≤ s u.val.length := by
    have H := hzu.length_le
    rwa [sourcePayload_length_of_large M hM x s hs u, hzlen] at H
  apply sourceTail_suffix_of_payload_suffix M hM x s hzu
  · exact (min_le_right _ _).trans (hb (hmin _ hun hlen))
  · simpa only [hzlen] using min_le_left l (suffixLength M s m)
end BalanceSpecification.MarkerExtension
