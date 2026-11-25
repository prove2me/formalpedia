-- Prove2me | solution 1 for Erdos654Proof.xh_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:51:21.988422+00:00
-- url     : https://prove2.me/submissions/faa2dacb-7b63-4432-80e2-029a883d6142

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
theorem _root_.solution (p : Bool × ℕ) : (xh p : ℝ) ^ 2 = ((p.2 : ℝ) + 1) ^ 2 := by
  have h : xh p ^ 2 = ((p.2 : ℤ) + 1) ^ 2 := by unfold xh; split <;> ring
  exact_mod_cast h
end Erdos654Proof
