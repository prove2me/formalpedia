-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.Walk.mem_pCover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:52:23.759082+00:00
-- url     : https://prove2.me/submissions/968f0179-e921-4ad5-9386-f736745be94d

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Theorems.Thm_BalanceSpecification_OneSidedExample_mem_vertexWords
public import Theorems.Thm_BalanceSpecification_OneSidedExample_length_runWord
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
attribute [local simp] BalanceSpecification.OneSidedExample.length_runWord
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
open Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
namespace Walk
theorem _root_.solution {i : ℕ} {t : Vertex} {w : Word Alphabet}
    (h : Walk (.p i) w t) : w ∈ pCover w.length := by
  generalize hn : w.length = n
  induction n generalizing i t w with
  | zero =>
    have hw : w = [] := List.length_eq_zero_iff.mp hn
    simp only [hw, pCover, Finset.mem_singleton]
  | succ n ih =>
    cases w with
    | nil => simp only [List.length_nil] at hn; omega
    | cons d w =>
      have hwlen : w.length = n := by simp only [List.length_cons] at hn; omega
      cases h with
      | cons he hw =>
        simp only [pCover, Finset.mem_union, Finset.mem_image]
        cases he with
        | pa => exact Or.inl (Or.inl ⟨w, mem_vertexWords.mpr ⟨hwlen, _, hw⟩, rfl⟩)
        | pc i => exact Or.inr ⟨w, mem_vertexWords.mpr ⟨hwlen, _, hw⟩, rfl⟩
        | pb i => exact Or.inl (Or.inr ⟨w, ih hw hwlen, rfl⟩)
end Walk
end BalanceSpecification.OneSidedExample
