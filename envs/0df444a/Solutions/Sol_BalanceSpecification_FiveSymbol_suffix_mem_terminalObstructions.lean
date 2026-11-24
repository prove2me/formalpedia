-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.suffix_mem_terminalObstructions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:40.36804+00:00
-- url     : https://prove2.me/submissions/743b6371-53d4-4668-ad04-96c079f6ab90

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
public import Theorems.Thm_BalanceSpecification_FiveSymbol_index_le_markerLength
public import Theorems.Thm_BalanceSpecification_FiveSymbol_short_suffix_forbiddenWord
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
theorem _root_.solution {s : Word Alphabet} {j l : ℕ}
    (hs : s <:+ forbiddenWord j) (hlen : s.length = l) (hl : 0 < l) :
    s ∈ terminalObstructions l := by
  by_cases hshort : l ≤ markerLength j + 1
  · apply Finset.mem_union_left
    exact Finset.mem_singleton.mpr (short_suffix_forbiddenWord hs hlen hl hshort)
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_range.mpr ?_, ?_⟩
    · have := index_le_markerLength j
      omega
    · symm
      simpa only [hlen] using (List.suffix_iff_eq_drop.mp hs)
end BalanceSpecification.FiveSymbol
