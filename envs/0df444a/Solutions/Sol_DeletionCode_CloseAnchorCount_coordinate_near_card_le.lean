-- Prove2me | solution 1 for DeletionCode.CloseAnchorCount.coordinate_near_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:05.267398+00:00
-- url     : https://prove2.me/submissions/035fef52-34d0-4a18-b76d-18ed28411393

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_CloseAnchorCount
import Theorems.Thm_DeletionCode_CloseAnchorCount_near_card_le
import Theorems.Thm_DeletionCode_CloseAnchorCount_coordinate_constraint_card_le

set_option autoImplicit true
open DeletionCode DeletionCode.CloseAnchorCount
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
namespace DeletionCode.CloseAnchorCount
theorem _root_.solution {r n : ℕ} (i : Fin (r + 1))
    (c : (Fin r → Fin n) → ℕ) (B : ℕ) :
    (univ.filter (fun a : Fin (r + 1) → Fin n =>
      Nat.dist (a i).val (c (i.removeNth a)) < B)).card ≤ (2 * B) * n ^ r := by
  have h := coordinate_constraint_card_le i (fun b x => Nat.dist x.val (c b) < B) (2 * B)
    (fun b => by
      apply le_of_eq_of_le ?_ (near_card_le n (c b) B)
      apply congrArg Finset.card
      ext x
      simp only [mem_filter, mem_univ, true_and])
  apply le_of_eq_of_le ?_ h
  apply congrArg Finset.card
  ext a
  simp only [mem_filter, mem_univ, true_and]
end DeletionCode.CloseAnchorCount
