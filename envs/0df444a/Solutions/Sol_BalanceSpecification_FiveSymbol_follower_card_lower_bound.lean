-- Prove2me | solution 1 for BalanceSpecification.FiveSymbol.follower_card_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:14.549023+00:00
-- url     : https://prove2.me/submissions/dd2e4345-01f0-4c80-a70e-e2441faef6fe

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
public import Theorems.Thm_BalanceSpecification_FiveSymbol_bad_follower_card_le_sum
public import Theorems.Thm_BalanceSpecification_FiveSymbol_weighted_wordCount_sum_le

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol
namespace BalanceSpecification.FiveSymbol
theorem _root_.solution {u : Word Alphabet} (hu : u ∈ language shift) (n : ℕ) :
    (5 / 9 : ℝ) * wordCount (language shift) n ≤
      (followerFinset (language shift) u n).card := by
  classical
  have hbadN := bad_follower_card_le_sum hu n
  have hbadcast : (((wordFinset (language shift) n) \ followerFinset (language shift) u n).card : ℝ) ≤
      ∑ l ∈ Finset.Icc 1 n, (l : ℝ) * wordCount (language shift) (n - l) := by
    exact_mod_cast hbadN
  have hbad : (((wordFinset (language shift) n) \ followerFinset (language shift) u n).card : ℝ) ≤
      (4 / 9 : ℝ) * wordCount (language shift) n :=
    hbadcast.trans (weighted_wordCount_sum_le n)
  have hsplitN := Finset.card_sdiff_add_card_eq_card
    (show followerFinset (language shift) u n ⊆ wordFinset (language shift) n from
      Finset.filter_subset _ _)
  have hsplit : (((wordFinset (language shift) n) \ followerFinset (language shift) u n).card : ℝ) +
      (followerFinset (language shift) u n).card = wordCount (language shift) n := by
    exact_mod_cast hsplitN
  linarith only [hbad, hsplit]
end BalanceSpecification.FiveSymbol
