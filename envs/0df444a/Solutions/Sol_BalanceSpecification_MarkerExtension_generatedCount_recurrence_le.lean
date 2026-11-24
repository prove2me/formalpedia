-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.generatedCount_recurrence_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:26.373208+00:00
-- url     : https://prove2.me/submissions/d7c4d502-0260-4c5f-9cdc-ccb6e23ce47f

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_RenewalBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkedRenewal
public import Theorems.Thm_BalanceSpecification_MarkerExtension_generator_length_pos
public import Theorems.Thm_BalanceSpecification_MarkerExtension_generated_first_generator
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
variable {A : Type*} [Fintype A]
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution (P : Set (Word A)) (n : ℕ) :
    generatedCount P (n + 1) ≤
      ∑ l ∈ Finset.range (n + 1), generatorCount P (l + 1) * generatedCount P (n - l) := by
  classical
  let T := (Finset.range (n + 1)).sigma fun l =>
    (wordFinset (markedCode P) (l + 1)).product
      (wordFinset (generatedWords (markedCode P)) (n - l))
  calc
    generatedCount P (n + 1) ≤ T.card := by
      apply Finset.card_le_card_of_surjOn
        (fun z : (l : ℕ) × (Word (Option A) × Word (Option A)) => z.2.1 ++ z.2.2)
      intro w hw
      obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
      obtain ⟨g, hg, v, hv, heq⟩ := generated_first_generator hwL (by omega)
      have hgpos := generator_length_pos hg
      have hlen := congrArg List.length heq
      simp only [List.length_append] at hlen
      let l := g.length - 1
      have hlrange : l ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by dsimp only [l]; omega)
      have hglen : g.length = l + 1 := by dsimp only [l]; omega
      have hvlen : v.length = n - l := by dsimp only [l]; omega
      exact ⟨⟨l, (g, v)⟩, Finset.mem_sigma.mpr ⟨hlrange, Finset.mem_product.mpr
        ⟨mem_wordFinset.mpr ⟨hg, hglen⟩, mem_wordFinset.mpr ⟨hv, hvlen⟩⟩⟩, heq⟩
    _ = ∑ l ∈ Finset.range (n + 1), generatorCount P (l + 1) * generatedCount P (n - l) := by
      simp only [T, Finset.card_sigma, generatorCount, generatedCount, wordCount]
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.card_product _ _
end BalanceSpecification.MarkerExtension
