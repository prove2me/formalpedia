-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.qCover_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:21.837854+00:00
-- url     : https://prove2.me/submissions/bebcb3e0-4bb9-4108-90f5-0a8190b79f75

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Theorems.Thm_BalanceSpecification_OneSidedExample_pCover_card_bound

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution (n : ℕ) : (qCover n).card + n + 1 ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have H : (qCover (n + 1)).card ≤ (qCover n).card + (pCover n).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
    have hP := pCover_card_bound n
    have hp : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by rw [pow_succ]; omega
    omega
end BalanceSpecification.OneSidedExample
