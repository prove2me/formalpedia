-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.marked_generated_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:22:28.381126+00:00
-- url     : https://prove2.me/submissions/fc60f6ab-b6b6-4d8d-b814-a66e3fdee31f

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
theorem _root_.solution {P : Set (Word A)} (hP : P.Nonempty)
    {z w : Word (Option A)} (hz : z ∈ generatedWords (markedCode P))
    (hw : none ∉ w) (hsuffix : w <:+ z) : ∃ v ∈ P, w <:+ v.map some := by
  by_cases hwnil : w = []
  · obtain ⟨v, hv⟩ := hP
    exact ⟨v, hv, by simp only [hwnil, List.nil_suffix]⟩
  obtain ⟨ws, hws, rfl⟩ := hz
  have hwsne : ws ≠ [] := by
    intro hnil
    subst ws
    have he := List.eq_nil_of_infix_nil hsuffix.isInfix
    exact hwnil he
  let g := ws.getLast hwsne
  have hg : g ∈ markedCode P := hws g (List.getLast_mem hwsne)
  obtain ⟨v, hv, hgv⟩ := hg
  have hgsuffix : g <:+ ws.flatten := by
    refine ⟨ws.dropLast.flatten, ?_⟩
    have H := congrArg List.flatten (List.dropLast_concat_getLast hwsne)
    simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using H
  rcases List.suffix_or_suffix_of_suffix hsuffix hgsuffix with hshort | hlong
  · rw [hgv] at hshort
    rcases List.suffix_cons_iff.mp hshort with heq | hsub
    · exact False.elim (hw (by rw [heq]; exact List.mem_cons_self))
    · exact ⟨v, hv, hsub⟩
  · exact False.elim (hw (hlong.isInfix.mem (by rw [hgv]; exact List.mem_cons_self)))
end BalanceSpecification.MarkerExtension
