-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.marker_isSynchronizing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:24:39.672428+00:00
-- url     : https://prove2.me/submissions/f552ac39-397e-4a46-9cba-591ed7bf94d7

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Theorems.Thm_BalanceSpecification_MarkerExtension_marked_generated_cut
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_append_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_language_codedShift_infix_generatedWords
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_generatedWords_of_mem
public import Theorems.Thm_BalanceSpecification_mem_language_codedShift_iff
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
omit [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution {P : Set (Word A)} (hP : P.Nonempty) :
    IsSynchronizing (language (codedShift (markedCode P))) [none] := by
  obtain ⟨v, hv⟩ := hP
  have hC : ∃ z ∈ markedCode P, 0 < z.length :=
    ⟨none :: v.map some, ⟨v, hv, rfl⟩, by simp only [List.length_cons]; omega⟩
  have hmarker : ([none] : Word (Option A)) ∈ language (codedShift (markedCode P)) := by
    apply (mem_language_codedShift_iff hC).mpr
    refine ⟨none :: v.map some, mem_generatedWords_of_mem ⟨v, hv, rfl⟩, [], v.map some, ?_⟩
    simp only [List.nil_append, List.singleton_append]
  refine ⟨hmarker, ?_⟩
  intro u w hu hw
  obtain ⟨U, hU, a, b, hUeq⟩ := language_codedShift_infix_generatedWords hu
  obtain ⟨W, hW, c, d, hWeq⟩ := language_codedShift_infix_generatedWords hw
  have hUeq' : U = (a ++ u) ++ none :: b := by
    rw [← hUeq]
    simp only [List.append_assoc, List.singleton_append]
  have hWeq' : W = c ++ none :: (w ++ d) := by
    rw [← hWeq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hleft := (marked_generated_cut hU hUeq').1
  have hright := (marked_generated_cut hW hWeq').2
  apply (mem_language_codedShift_iff hC).mpr
  refine ⟨(a ++ u) ++ (none :: (w ++ d)), append_mem_generatedWords hleft hright,
    a, d, ?_⟩
  simp only [List.append_assoc, List.cons_append, List.nil_append]
end BalanceSpecification.MarkerExtension
