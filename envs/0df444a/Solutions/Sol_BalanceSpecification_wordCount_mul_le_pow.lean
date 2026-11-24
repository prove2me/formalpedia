-- Prove2me | solution 1 for BalanceSpecification.wordCount_mul_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:49.405006+00:00
-- url     : https://prove2.me/submissions/8a1dd5cc-e6c1-4072-8206-e0cc10768dac

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_add_le
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
public import Theorems.Thm_BalanceSpecification_wordCount_zero_le_one
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}
variable [Fintype A]
namespace BalanceSpecification
theorem _root_.solution {L : Set (Word A)} (hL : IsFactorial L) (n k : ℕ) :
    wordCount L (k * n) ≤ (wordCount L n) ^ k := by
  induction k with
  | zero => simpa only [zero_mul, pow_zero] using wordCount_zero_le_one L
  | succ k ih =>
    calc
      wordCount L ((k + 1) * n) = wordCount L (k * n + n) := by rw [Nat.add_mul, one_mul]
      _ ≤ wordCount L (k * n) * wordCount L n := wordCount_add_le hL _ _
      _ ≤ (wordCount L n) ^ k * wordCount L n := Nat.mul_le_mul_right _ ih
      _ = (wordCount L n) ^ (k + 1) := (pow_succ _ _).symm
end BalanceSpecification
