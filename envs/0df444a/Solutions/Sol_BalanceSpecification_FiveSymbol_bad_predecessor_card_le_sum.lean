-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.bad_predecessor_card_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:26.956218+00:00
-- url     : https://prove2.me/submissions/053b6041-b3cd-49f3-a2c9-72c5c20f5ee9

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
public import Theorems.Thm_BalanceSpecification_FiveSymbol_bad_predecessor_mem_crossing_cover
public import Theorems.Thm_BalanceSpecification_FiveSymbol_leftCrossingCover_card_le
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_shortlexWord_zero
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.shortlexWord_zero
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution {u : Word Alphabet} (hu : u ∈ language shift) (n : ℕ) :
    ((wordFinset (language shift) n) \ predecessorFinset (language shift) u n).card ≤
      ∑ l ∈ Finset.Icc 1 n, l * wordCount (language shift) (n - l) := by
  classical
  have hsub : (wordFinset (language shift) n) \ predecessorFinset (language shift) u n ⊆
      (Finset.Icc 1 n).biUnion (leftCrossingCover n) := by
    intro v hv
    obtain ⟨hvW, hnot⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨hvL, hvlen⟩ := mem_wordFinset.mp hvW
    have hbad : v ++ u ∉ language shift := by
      intro hvu
      exact hnot (mem_predecessorFinset.mpr ⟨hvL, hvlen, hvu⟩)
    obtain ⟨l, hl, hln, hcov⟩ := bad_predecessor_mem_crossing_cover hu hvL hbad
    exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_Icc.mpr ⟨hl, by omega⟩,
      by simpa only [hvlen] using hcov⟩
  calc
    _ ≤ ((Finset.Icc 1 n).biUnion (leftCrossingCover n)).card := Finset.card_le_card hsub
    _ ≤ ∑ l ∈ Finset.Icc 1 n, (leftCrossingCover n l).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum (fun l hl => leftCrossingCover_card_le n
      (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hl).1))
end BalanceSpecification.FiveSymbol
