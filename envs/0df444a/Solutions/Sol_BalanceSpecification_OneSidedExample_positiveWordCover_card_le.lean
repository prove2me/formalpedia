-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.positiveWordCover_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:52:18.751793+00:00
-- url     : https://prove2.me/submissions/e51880a8-75a1-4bd9-b6e5-16610fe2ad7f

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedBounds
public import Theorems.Thm_BalanceSpecification_OneSidedExample_vertexWords_card
public import Theorems.Thm_BalanceSpecification_OneSidedExample_pCover_card_bound
public import Theorems.Thm_BalanceSpecification_OneSidedExample_qCover_card_bound

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution (n : ℕ) : (positiveWordCover n).card ≤ 5 * 2 ^ n := by
  have H : (positiveWordCover n).card ≤ (qCover n).card + (pCover n).card + 2 ^ n := by
    unfold positiveWordCover
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add ((Finset.card_union_le _ _).trans
        (Nat.add_le_add Finset.card_image_le Finset.card_image_le))
        (Finset.card_image_le.trans_eq (vertexWords_card _ _)))
  have hP := pCover_card_bound n
  have hQ := qCover_card_bound n
  have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; omega
  omega
end BalanceSpecification.OneSidedExample
