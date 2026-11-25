-- Prove2me | solution 1 for Erdos654Proof.card_idx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:44:26.152505+00:00
-- url     : https://prove2.me/submissions/fea5176b-0fe3-429a-bd8c-26b4052a4288

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
theorem _root_.solution (m : ℕ) : #(idx m) = 2 * m := by simp [idx]
end Erdos654Proof
