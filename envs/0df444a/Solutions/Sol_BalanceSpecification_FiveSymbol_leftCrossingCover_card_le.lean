-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.leftCrossingCover_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:54.997855+00:00
-- url     : https://prove2.me/submissions/17a23f9a-814f-43fe-96ba-764fa98e64cc

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
public import Theorems.Thm_BalanceSpecification_FiveSymbol_initialObstructions_card_le
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
theorem _root_.solution (n : ℕ) {l : ℕ} (hl : 0 < l) :
    (leftCrossingCover n l).card ≤ l * wordCount (language shift) (n - l) := by
  calc
    (leftCrossingCover n l).card ≤
        ∑ s ∈ initialObstructions l,
          ((wordFinset (language shift) (n - l)).image (fun t => t ++ s)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ initialObstructions l, wordCount (language shift) (n - l) := by
      exact Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
    _ = (initialObstructions l).card * wordCount (language shift) (n - l) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    _ ≤ l * wordCount (language shift) (n - l) :=
      Nat.mul_le_mul_right _ (initialObstructions_card_le hl)
end BalanceSpecification.FiveSymbol
