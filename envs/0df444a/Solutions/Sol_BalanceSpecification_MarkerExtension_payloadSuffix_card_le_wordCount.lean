-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.payloadSuffix_card_le_wordCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:39.792857+00:00
-- url     : https://prove2.me/submissions/637cfa54-b1c1-4a01-91d5-4165f9a4fde3

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix
public import Theorems.Thm_BalanceSpecification_MarkerExtension_mem_payloadSuffixFinset
public import Theorems.Thm_BalanceSpecification_MarkerExtension_payloadSuffix_common_tail
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
    (hmin : ∀ n : ℕ, 1 ≤ n → l ≤ s n → m ≤ n) :
    (payloadSuffixFinset M hM x s l).card ≤
      wordCount (language Y) (l - min l (suffixLength M s m)) := by
  classical
  let t := min l (suffixLength M s m)
  change (payloadSuffixFinset M hM x s l).card ≤
    (wordFinset (language Y) (l - t)).card
  apply Finset.card_le_card_of_injOn (fun z : Word A => z.take (l - t))
  · intro z hz
    obtain ⟨hzY, hzlen, _⟩ := (mem_payloadSuffixFinset M hM x s).mp hz
    exact mem_wordFinset.mpr
      ⟨language_factorial Y (List.take_prefix _ z).isInfix hzY,
        by simp only [List.length_take, hzlen]; omega⟩
  · intro z hz w hw heq
    change z.take (l - t) = w.take (l - t) at heq
    have hzlen := ((mem_payloadSuffixFinset M hM x s).mp hz).2.1
    have hwlen := ((mem_payloadSuffixFinset M hM x s).mp hw).2.1
    have hzdrop : z.drop (l - t) = sourceTail x t := by
      have H := List.suffix_iff_eq_drop.mp (payloadSuffix_common_tail M hM x s hs hb hmin hz)
      simpa only [sourceTail, length_block, hzlen, t] using H.symm
    have hwdrop : w.drop (l - t) = sourceTail x t := by
      have H := List.suffix_iff_eq_drop.mp (payloadSuffix_common_tail M hM x s hs hb hmin hw)
      simpa only [sourceTail, length_block, hwlen, t] using H.symm
    calc
      z = z.take (l - t) ++ z.drop (l - t) := (List.take_append_drop _ _).symm
      _ = w.take (l - t) ++ w.drop (l - t) := by rw [heq, hzdrop, hwdrop]
      _ = w := List.take_append_drop _ _
end BalanceSpecification.MarkerExtension
