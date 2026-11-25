-- Prove2me | solution 1 for Erdos654Proof.xpt_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:56:03.095416+00:00
-- url     : https://prove2.me/submissions/78ed9bbd-6d56-4e96-9a36-390a5a4e1d60

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
public import Theorems.Thm_Erdos654Proof_xpt_zero
public import Theorems.Thm_Erdos654Proof_xpt_one
public import Theorems.Thm_Erdos654Proof_ypt_zero
public import Theorems.Thm_Erdos654Proof_ypt_one
public import Theorems.Thm_Erdos654Proof_xh_injective
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
theorem _root_.solution : Function.Injective xpt := by
  intro p q h
  have := congrArg (· 0) h
  simp only [xpt_zero, mul_eq_mul_left_iff, Int.cast_inj] at this
  exact xh_injective (this.resolve_right two_ne_zero)
end Erdos654Proof
