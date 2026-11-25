-- Prove2me | solution 1 for Erdos654Proof.distinctDistancesFrom_union_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:56:47.375047+00:00
-- url     : https://prove2.me/submissions/a86156eb-fe58-481e-bf87-25ceb67cab0c

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
public import Theorems.Thm_Erdos654Proof_card_image_erase_le

set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof
namespace Erdos654Proof
theorem _root_.solution (B C : Finset ℝ²) {x : ℝ²} (hx : x ∈ B) :
    distinctDistancesFrom (B ∪ C) x ≤ (#B - 1) + #(C.image fun y ↦ dist y x) := by
  unfold distinctDistancesFrom
  convert card_image_erase_le (B ∪ C) B C (fun y hy ↦ mem_union.1 hy) hx
end Erdos654Proof
