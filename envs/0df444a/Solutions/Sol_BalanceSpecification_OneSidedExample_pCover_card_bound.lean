-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.pCover_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:33.580602+00:00
-- url     : https://prove2.me/submissions/28f108c2-ea8c-4f69-bca6-ff5db1557fd0

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Theorems.Thm_BalanceSpecification_OneSidedExample_vertexWords_card

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution (n : ℕ) : (pCover n).card + 1 ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have H : (pCover (n + 1)).card ≤ 2 ^ n + (pCover n).card + 2 ^ n := by
      rw [pCover]
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add ((Finset.card_union_le _ _).trans
          (Nat.add_le_add (Finset.card_image_le.trans_eq (vertexWords_card _ _))
            Finset.card_image_le)) (Finset.card_image_le.trans_eq (vertexWords_card _ _)))
    have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; omega
    have hp' : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by rw [pow_succ]; omega
    omega
end BalanceSpecification.OneSidedExample
