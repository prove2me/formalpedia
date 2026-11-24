-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.rightBalanced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:32.013236+00:00
-- url     : https://prove2.me/submissions/ec868402-c787-4083-9f62-3b825b034770

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Theorems.Thm_BalanceSpecification_OneSidedExample_wordCount_upper_bound
public import Theorems.Thm_BalanceSpecification_OneSidedExample_follower_card_lower_bound
public import Theorems.Thm_BalanceSpecification_OneSidedExample_nonempty
public import Theorems.Thm_BalanceSpecification_wordCount_pos_of_nonempty


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution : RightBalanced (language shift) := by
  refine ⟨2 / 5, by norm_num, ?_⟩
  intro u hu n hn
  have hpos : (0 : ℝ) < wordCount (language shift) n := by
    exact_mod_cast wordCount_pos_of_nonempty nonempty n
  apply (le_div_iff₀ hpos).mpr
  cases n with
  | zero => omega
  | succ m =>
    have hF : (2 : ℝ) ^ (m + 1) ≤ (followerFinset (language shift) u (m + 1)).card := by
      exact_mod_cast follower_card_lower_bound hu (m + 1)
    have hB : (wordCount (language shift) (m + 1) : ℝ) ≤ 5 * (2 : ℝ) ^ m := by
      exact_mod_cast wordCount_upper_bound m
    rw [pow_succ] at hF
    linarith only [hF, hB]
end BalanceSpecification.OneSidedExample
