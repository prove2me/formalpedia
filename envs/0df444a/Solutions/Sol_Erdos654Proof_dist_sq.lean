-- Prove2me | solution 1 for Erdos654Proof.dist_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:38:07.350597+00:00
-- url     : https://prove2.me/submissions/3b6cfa58-1303-4fc0-8e58-45edc71a65d4

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
theorem _root_.solution (P Q : ℝ²) : dist P Q ^ 2 = (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]
end Erdos654Proof
