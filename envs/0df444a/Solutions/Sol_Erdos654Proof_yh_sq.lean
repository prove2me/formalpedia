-- Prove2me | solution 1 for Erdos654Proof.yh_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:51:31.13667+00:00
-- url     : https://prove2.me/submissions/30680253-ee50-4b7a-86b9-5651b4a5c1c7

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution

set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof
namespace Erdos654Proof
theorem _root_.solution (p : Bool × ℕ) : (2 * (yh p : ℝ) + 1) ^ 2 = (2 * (p.2 : ℝ) + 1) ^ 2 := by
  have h : (2 * yh p + 1) ^ 2 = (2 * (p.2 : ℤ) + 1) ^ 2 := by unfold yh; split <;> ring
  exact_mod_cast h
end Erdos654Proof
