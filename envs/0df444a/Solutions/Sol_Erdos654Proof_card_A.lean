-- Prove2me | solution 1 for Erdos654Proof.card_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:04:58.838478+00:00
-- url     : https://prove2.me/submissions/f78f520b-3ad1-444e-a96b-2505ec45a482

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
public import Theorems.Thm_Erdos654Proof_card_XS
public import Theorems.Thm_Erdos654Proof_card_YS
public import Theorems.Thm_Erdos654Proof_disjoint_XS_YS

set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof
namespace Erdos654Proof
theorem _root_.solution (m : ℕ) : #(A m) = 4 * m := by
  rw [A, card_union_of_disjoint (disjoint_XS_YS m), card_XS, card_YS]
  ring
end Erdos654Proof
