-- Prove2me | solution 1 for Erdos654Proof.dist_xpt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:56:33.979898+00:00
-- url     : https://prove2.me/submissions/43e22963-e20d-45b9-95f5-417769859d53

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
public import Theorems.Thm_Erdos654Proof_dist_sq
public import Theorems.Thm_Erdos654Proof_xpt_zero
public import Theorems.Thm_Erdos654Proof_xpt_one
public import Theorems.Thm_Erdos654Proof_ypt_zero
public import Theorems.Thm_Erdos654Proof_ypt_one
public import Theorems.Thm_Erdos654Proof_xh_sq
public import Theorems.Thm_Erdos654Proof_dist_eq_of_sq_eq
attribute [local simp] Erdos654Proof.xpt_zero
attribute [local simp] Erdos654Proof.xpt_one
attribute [local simp] Erdos654Proof.ypt_zero
attribute [local simp] Erdos654Proof.ypt_one

set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof
namespace Erdos654Proof
theorem _root_.solution (p q : Bool × ℕ) : dist (xpt q) (ypt p) = dist (xpt (true, q.2)) (ypt p) := by
  apply dist_eq_of_sq_eq
  rw [dist_sq, dist_sq]
  simp only [ypt_zero, ypt_one, xpt_zero, xpt_one, zero_sub]
  have h1 := xh_sq q
  have h2 := xh_sq (true, q.2)
  nlinarith [h1, h2]
end Erdos654Proof
