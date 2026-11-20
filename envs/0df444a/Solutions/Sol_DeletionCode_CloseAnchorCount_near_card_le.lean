-- Prove2me | solution 1 for DeletionCode.CloseAnchorCount.near_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:54.334851+00:00
-- url     : https://prove2.me/submissions/5a7af84e-ab1f-4dd6-bd84-8233c50b9f2e

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_CloseAnchorCount

set_option autoImplicit true
open DeletionCode DeletionCode.CloseAnchorCount
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
namespace DeletionCode.CloseAnchorCount
theorem _root_.solution (n c B : ℕ) :
    (univ.filter (fun x : Fin n => Nat.dist x.val c < B)).card ≤ 2 * B := by
  calc
    (univ.filter (fun x : Fin n => Nat.dist x.val c < B)).card ≤
        (range (2 * B)).card := by
      apply Finset.card_le_card_of_injOn (fun x : Fin n => x.val + B - c)
      · intro x hx
        have hd := (mem_filter.mp hx).2
        change x.val + B - c ∈ range (2 * B)
        rw [mem_range]
        unfold Nat.dist at hd
        omega
      · intro x hx y hy heq
        have hx' := (mem_filter.mp hx).2
        have hy' := (mem_filter.mp hy).2
        change x.val + B - c = y.val + B - c at heq
        unfold Nat.dist at hx' hy'
        apply Fin.ext
        omega
    _ = 2 * B := card_range _
end DeletionCode.CloseAnchorCount
