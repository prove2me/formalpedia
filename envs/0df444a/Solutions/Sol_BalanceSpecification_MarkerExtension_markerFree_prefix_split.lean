-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.markerFree_prefix_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:21:59.136853+00:00
-- url     : https://prove2.me/submissions/7b7adc4c-28ac-4914-aac4-f824d5b182e3

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
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
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution {s t p q : Word (Option A)}
    (hs : none ∉ s) (heq : s ++ t = p ++ none :: q) :
    ∃ r : Word (Option A), p = s ++ r ∧ t = r ++ none :: q := by
  induction s generalizing p with
  | nil => exact ⟨p, rfl, heq⟩
  | cons a s ih =>
    cases p with
    | nil =>
      have ha : a = none := (List.cons.inj heq).1
      exact False.elim (hs (List.mem_cons.mpr (Or.inl ha.symm)))
    | cons b p =>
      have hab : a = b := (List.cons.inj heq).1
      have htail : s ++ t = p ++ none :: q := (List.cons.inj heq).2
      obtain ⟨r, hr, ht⟩ := ih
        (fun hn => hs (List.mem_cons_of_mem a hn)) htail
      refine ⟨r, ?_, ht⟩
      simp only [List.cons_append, hab, hr]
end BalanceSpecification.MarkerExtension
