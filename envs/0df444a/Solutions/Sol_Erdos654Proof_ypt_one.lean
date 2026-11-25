-- Prove2me | solution 1 for Erdos654Proof.ypt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:38:35.571564+00:00
-- url     : https://prove2.me/submissions/84f841ca-5652-46cc-b259-5cad896835d4

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
theorem _root_.solution (p : Bool × ℕ) : ypt p 1 = 2 * (yh p : ℝ) + 1 := rfl
end Erdos654Proof
