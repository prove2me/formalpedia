-- Prove2me | solution 1 for Erdos654Proof.dist_ypt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:56:14.088804+00:00
-- url     : https://prove2.me/submissions/c1e7fb79-afff-47cf-b2bf-15641dd2bdba

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
public import Theorems.Thm_Erdos654Proof_dist_sq
public import Theorems.Thm_Erdos654Proof_xpt_zero
public import Theorems.Thm_Erdos654Proof_xpt_one
public import Theorems.Thm_Erdos654Proof_ypt_zero
public import Theorems.Thm_Erdos654Proof_ypt_one
public import Theorems.Thm_Erdos654Proof_yh_sq
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
theorem _root_.solution (p q : Bool × ℕ) : dist (ypt q) (xpt p) = dist (ypt (true, q.2)) (xpt p) := by
  apply dist_eq_of_sq_eq
  rw [dist_sq, dist_sq]
  simp only [ypt_zero, ypt_one, xpt_zero, xpt_one, sub_zero]
  rw [yh_sq q, yh_sq (true, q.2)]
end Erdos654Proof
