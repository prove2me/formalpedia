-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.biBalanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:00.987734+00:00
-- url     : https://prove2.me/submissions/ec53afb1-5edb-4887-b5f2-ce6c9ef334f4

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
public import Theorems.Thm_BalanceSpecification_FiveSymbol_follower_card_lower_bound
public import Theorems.Thm_BalanceSpecification_FiveSymbol_predecessor_card_lower_bound
public import Theorems.Thm_BalanceSpecification_FiveSymbol_shift_nonempty
public import Theorems.Thm_BalanceSpecification_wordCount_pos_of_nonempty


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution : BiBalanced (language shift) := by
  have hpos (n : ℕ) : (0 : ℝ) < wordCount (language shift) n := by
    exact_mod_cast wordCount_pos_of_nonempty shift_nonempty n
  constructor
  · refine ⟨5 / 9, by norm_num, ?_⟩
    intro u hu n _
    exact (le_div_iff₀ (hpos n)).mpr (follower_card_lower_bound hu n)
  · refine ⟨5 / 9, by norm_num, ?_⟩
    intro u hu n _
    exact (le_div_iff₀ (hpos n)).mpr (predecessor_card_lower_bound hu n)
end BalanceSpecification.FiveSymbol
