-- Prove2me | solution 1 for Erdos654Proof.xh_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:51:11.870439+00:00
-- url     : https://prove2.me/submissions/5a631bfd-097f-4681-ae57-215ae7794400

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
theorem _root_.solution : Function.Injective xh := by
  rintro ⟨σ, i⟩ ⟨τ, k⟩ h
  cases σ <;> cases τ <;> simp [xh] at h ⊢ <;> omega
end Erdos654Proof
