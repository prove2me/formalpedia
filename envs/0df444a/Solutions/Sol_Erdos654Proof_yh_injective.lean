-- Prove2me | solution 1 for Erdos654Proof.yh_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:51:19.269803+00:00
-- url     : https://prove2.me/submissions/17e28416-eb0b-479f-aece-5ab806870471

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
theorem _root_.solution : Function.Injective yh := by
  rintro ⟨σ, i⟩ ⟨τ, k⟩ h
  cases σ <;> cases τ <;> simp [yh] at h ⊢ <;> omega
end Erdos654Proof
