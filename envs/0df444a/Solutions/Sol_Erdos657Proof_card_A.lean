-- Prove2me | solution 1 for Erdos657Proof.card_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:04:51.581857+00:00
-- url     : https://prove2.me/submissions/ef7c1778-7a7e-49a8-96bb-815c97f91469

module
public import Mathlib
public import Definitions.Def_Erdos657Palomar_Solution
public import Theorems.Thm_Erdos657Proof_pt_injective

set_option autoImplicit true
@[expose] public section
public section
open scoped Finset
open Filter
open scoped EuclideanGeometry
open Erdos657Proof
open Finset
namespace Erdos657Proof
theorem _root_.solution (k : ℕ) : #(univ.image pt : Finset (ℝ^k)) = 2 ^ k := by
  rw [card_image_of_injective _ (pt_injective k), card_univ, Fintype.card_finset,
    Fintype.card_fin]
end Erdos657Proof
