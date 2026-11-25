-- Prove2me | solution 1 for Erdos654Proof.A_subset_axes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:51:48.578002+00:00
-- url     : https://prove2.me/submissions/557acf14-c411-4983-b7f8-e7506f2a0a0b

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
theorem _root_.solution (m : ℕ) : (A m : Set ℝ²) ⊆ XAxis ∪ YAxis := by
  intro P hP
  simp only [A, XS, YS, coe_union, coe_image, Set.mem_union, Set.mem_image] at hP
  rcases hP with ⟨p, -, rfl⟩ | ⟨p, -, rfl⟩
  · exact Or.inl ⟨rfl, xh p, rfl⟩
  · exact Or.inr ⟨rfl, yh p, rfl⟩
end Erdos654Proof
