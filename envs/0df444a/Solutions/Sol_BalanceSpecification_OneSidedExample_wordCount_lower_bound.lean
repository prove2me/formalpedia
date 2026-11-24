-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.wordCount_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:53:29.093804+00:00
-- url     : https://prove2.me/submissions/d059efef-4a35-4a3f-b6b7-b0fdb2078aec

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Theorems.Thm_BalanceSpecification_OneSidedExample_follower_card_lower_bound
public import Theorems.Thm_BalanceSpecification_OneSidedExample_nonempty
public import Theorems.Thm_BalanceSpecification_follower_card_le
public import Theorems.Thm_BalanceSpecification_nil_mem_language_iff


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution (n : ℕ) : 2 ^ n ≤ wordCount (language shift) n :=
  (follower_card_lower_bound (nil_mem_language_iff.mpr nonempty) n).trans
    (follower_card_le _ _ _)
end BalanceSpecification.OneSidedExample
