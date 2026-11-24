-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.pow_four_mul_wordCount_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:53.147551+00:00
-- url     : https://prove2.me/submissions/f8db9963-b7d7-4a42-94b8-f512ea618beb

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
public import Theorems.Thm_BalanceSpecification_FiveSymbol_four_mul_wordCount_le
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
theorem _root_.solution (m l : ℕ) :
    4 ^ l * wordCount (language shift) m ≤ wordCount (language shift) (m + l) := by
  induction l with
  | zero => simp only [pow_zero, one_mul, Nat.add_zero]; exact le_rfl
  | succ l ih =>
    calc
      4 ^ (l + 1) * wordCount (language shift) m =
          4 * (4 ^ l * wordCount (language shift) m) := by rw [pow_succ]; ring
      _ ≤ 4 * wordCount (language shift) (m + l) := Nat.mul_le_mul_left _ ih
      _ ≤ wordCount (language shift) (m + (l + 1)) := by
        simpa only [Nat.add_assoc] using four_mul_wordCount_le (m + l)
end BalanceSpecification.FiveSymbol
