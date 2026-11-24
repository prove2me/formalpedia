-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.marked_ending_marker_normalForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:23:53.411188+00:00
-- url     : https://prove2.me/submissions/50aeff41-517e-441e-8a6d-d6dfa108f68f

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Theorems.Thm_BalanceSpecification_MarkerExtension_marked_generated_cut
public import Theorems.Thm_BalanceSpecification_MarkerExtension_split_first_marker
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_language_codedShift_infix_generatedWords
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
omit [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution {P : Set (Word A)} {z : Word (Option A)}
    (hz : z ++ [none] ∈ language (codedShift (markedCode P))) :
    ∃ a : Word A, ∃ c : Word (Option A),
      a.map some ++ [none] ∈ language (codedShift (markedCode P)) ∧
      c ∈ generatedWords (markedCode P) ∧ z ++ [none] = a.map some ++ c ++ [none] := by
  obtain ⟨a, c, hsplit, hc⟩ := split_first_marker z
  refine ⟨a, c, ?_, ?_, ?_⟩
  · apply language_factorial (codedShift (markedCode P)) (u := a.map some ++ [none])
      (v := z ++ [none]) _ hz
    rcases hc with rfl | ⟨t, rfl⟩
    · exact ⟨[], [], by simp only [List.nil_append, List.append_nil, hsplit]⟩
    · refine ⟨[], t ++ [none], ?_⟩
      simp only [List.nil_append, List.append_assoc, List.cons_append, List.nil_append,
        hsplit]
  · rcases hc with rfl | ⟨t, rfl⟩
    · exact nil_mem_generatedWords _
    · obtain ⟨W, hW, p, q, heq⟩ := language_codedShift_infix_generatedWords hz
      have hfirst : W = (p ++ a.map some) ++ none :: (t ++ none :: q) := by
        rw [← heq, hsplit]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      have hsuffix := (marked_generated_cut hW hfirst).2
      have hlast : none :: (t ++ none :: q) = (none :: t) ++ none :: q := by
        simp only [List.cons_append]
      exact (marked_generated_cut hsuffix hlast).1
  · rw [hsplit]
end BalanceSpecification.MarkerExtension
