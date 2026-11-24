-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.prefix_mem_initialObstructions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:44.296803+00:00
-- url     : https://prove2.me/submissions/a52602ee-0575-4b80-a33a-27cb34ad42c1

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
public import Theorems.Thm_BalanceSpecification_FiveSymbol_index_le_markerLength
public import Theorems.Thm_BalanceSpecification_FiveSymbol_short_prefix_forbiddenWord
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
    (hs : s <+: forbiddenWord j) (hlen : s.length = l) (hl : 0 < l) :
    s ∈ initialObstructions l := by
  by_cases hshort : l ≤ markerLength j + 1
  · apply Finset.mem_union_left
    exact Finset.mem_singleton.mpr (short_prefix_forbiddenWord hs hlen hl hshort)
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_range.mpr ?_, ?_⟩
    · have := index_le_markerLength j
      omega
    · symm
      simpa only [hlen] using (List.prefix_iff_eq_take.mp hs)
end BalanceSpecification.FiveSymbol
