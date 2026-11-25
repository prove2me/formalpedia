-- Prove2me | solution 1 for Erdos654Proof.disjoint_XS_YS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:51:43.183491+00:00
-- url     : https://prove2.me/submissions/a6668e7a-263a-4065-84a7-207c335dd33f

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
public import Theorems.Thm_Erdos654Proof_xpt_zero
public import Theorems.Thm_Erdos654Proof_xpt_one
public import Theorems.Thm_Erdos654Proof_ypt_zero
public import Theorems.Thm_Erdos654Proof_ypt_one
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
theorem _root_.solution (m : ℕ) : Disjoint (XS m) (YS m) := by
  rw [Finset.disjoint_left]
  simp only [XS, YS, mem_image]
  rintro _ ⟨p, -, rfl⟩ ⟨q, -, hq⟩
  have := congrArg (· 1) hq
  simp only [ypt_one, xpt_one] at this
  have : ((2 * yh q + 1 : ℤ) : ℝ) = ((0 : ℤ) : ℝ) := by push_cast; linarith
  have := Int.cast_injective this
  omega
end Erdos654Proof
