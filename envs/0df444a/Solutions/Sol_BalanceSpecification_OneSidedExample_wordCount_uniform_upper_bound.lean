-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.wordCount_uniform_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:32.516973+00:00
-- url     : https://prove2.me/submissions/ec638984-92d6-4f98-a830-b848b755fa14

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Theorems.Thm_BalanceSpecification_OneSidedExample_wordCount_upper_bound
public import Theorems.Thm_BalanceSpecification_wordCount_zero_le_one


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution (n : ℕ) :
    wordCount (language shift) n ≤ 5 * 2 ^ n := by
  cases n with
  | zero => exact (wordCount_zero_le_one _).trans (by decide)
  | succ m =>
    exact (wordCount_upper_bound m).trans (Nat.mul_le_mul_left 5
      (by rw [pow_succ]; omega))
end BalanceSpecification.OneSidedExample
