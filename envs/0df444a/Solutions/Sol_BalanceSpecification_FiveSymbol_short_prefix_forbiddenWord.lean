-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.short_prefix_forbiddenWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:30.011509+00:00
-- url     : https://prove2.me/submissions/26d5db11-5cbb-4d23-913b-fbe42313f503

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
    (hs : s <+: forbiddenWord j) (hlen : s.length = l) (hl : 0 < l)
    (hshort : l ≤ markerLength j + 1) :
    s = [0] ++ List.replicate (l - 1) 1 := by
  have hhead : [0] ++ List.replicate (markerLength j) 1 <+: forbiddenWord j := by
    refine ⟨[2] ++ shortlexWord j ++ markerRight j, ?_⟩
    simp only [forbiddenWord, markerLeft, List.append_assoc]
  have hsHead := List.prefix_of_prefix_length_le hs hhead
    (by simp only [List.length_append, List.length_replicate,
      List.length_singleton, hlen]; omega)
  rw [List.prefix_iff_eq_take] at hsHead
  rw [hlen] at hsHead
  cases l with
  | zero => omega
  | succ l =>
    simpa only [Nat.add_sub_cancel, List.singleton_append, List.take_succ_cons,
      List.take_replicate, Nat.min_eq_left (show l ≤ markerLength j by omega)] using hsHead
end BalanceSpecification.FiveSymbol
