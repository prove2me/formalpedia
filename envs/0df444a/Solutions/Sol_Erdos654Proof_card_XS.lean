-- Prove2me | solution 1 for Erdos654Proof.card_XS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:00:40.425576+00:00
-- url     : https://prove2.me/submissions/8a393e22-2c65-435f-8b53-408270b6c4d3

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
public import Theorems.Thm_Erdos654Proof_xpt_injective
public import Theorems.Thm_Erdos654Proof_card_idx

set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof
namespace Erdos654Proof
theorem _root_.solution (m : ℕ) : #(XS m) = 2 * m := by
  rw [XS, card_image_of_injective _ xpt_injective, card_idx]
end Erdos654Proof
