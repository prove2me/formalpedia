-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.short_suffix_forbiddenWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:29.332532+00:00
-- url     : https://prove2.me/submissions/de3dfc28-e690-4fd0-a318-cb754fc50216

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
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
    (hs : s <:+ forbiddenWord j) (hlen : s.length = l) (hl : 0 < l)
    (hshort : l ≤ markerLength j + 1) :
    s = List.replicate (l - 1) 1 ++ [4] := by
  have htail : List.replicate (markerLength j) 1 ++ [4] <:+ forbiddenWord j := by
    refine ⟨markerLeft j ++ shortlexWord j ++ [3], ?_⟩
    simp only [forbiddenWord, markerRight, List.append_assoc]
  have hsTail := List.suffix_of_suffix_length_le hs htail
    (by simp only [List.length_append, List.length_replicate,
      List.length_singleton, hlen]; exact hshort)
  rw [List.suffix_iff_eq_drop] at hsTail
  rw [hsTail]
  simp only [List.length_append, List.length_replicate, List.length_singleton, hlen]
  rw [List.drop_append_of_le_length (by simp only [List.length_replicate]; omega),
    List.drop_replicate]
  rw [show markerLength j - (markerLength j + 1 - l) = l - 1 by omega]
end BalanceSpecification.FiveSymbol
