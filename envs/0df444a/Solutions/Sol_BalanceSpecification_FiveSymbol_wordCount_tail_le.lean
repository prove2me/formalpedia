-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.wordCount_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:41.154871+00:00
-- url     : https://prove2.me/submissions/63c5a4f1-7282-4134-8e0c-3ce06b9c2bb3

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
public import Theorems.Thm_BalanceSpecification_FiveSymbol_pow_four_mul_wordCount_le
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
theorem _root_.solution {n l : ℕ} (hl : l ≤ n) :
    (wordCount (language shift) (n - l) : ℝ) ≤
      (1 / 4 : ℝ) ^ l * wordCount (language shift) n := by
  have Hnat := pow_four_mul_wordCount_le (n - l) l
  rw [Nat.sub_add_cancel hl] at Hnat
  have H : (4 : ℝ) ^ l * (wordCount (language shift) (n - l) : ℝ) ≤
      wordCount (language shift) n := by exact_mod_cast Hnat
  calc
    (wordCount (language shift) (n - l) : ℝ) ≤
        (wordCount (language shift) n : ℝ) / (4 : ℝ) ^ l :=
      (le_div_iff₀ (pow_pos (by norm_num) l)).mpr (by simpa only [mul_comm] using H)
    _ = (1 / 4 : ℝ) ^ l * wordCount (language shift) n := by rw [one_div_pow]; ring
end BalanceSpecification.FiveSymbol
