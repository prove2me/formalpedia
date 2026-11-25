-- Prove2me | solution 1 for Erdos654Proof.card_YS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:59:59.351801+00:00
-- url     : https://prove2.me/submissions/0113753e-aa13-4d44-b2c4-6bb54356a727

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
public import Theorems.Thm_Erdos654Proof_ypt_injective
public import Theorems.Thm_Erdos654Proof_card_idx

set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof
namespace Erdos654Proof
theorem _root_.solution (m : ℕ) : #(YS m) = 2 * m := by
  rw [YS, card_image_of_injective _ ypt_injective, card_idx]
end Erdos654Proof
