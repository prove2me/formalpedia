-- Prove2me | solution 1 for Erdos654Proof.noFourConcyclic_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:36:56.292638+00:00
-- url     : https://prove2.me/submissions/b35d55e1-7981-4b4f-9838-a6f6456c4eb8

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
public import Theorems.Thm_Erdos654Proof_noFourConcyclic_axes
public import Theorems.Thm_Erdos654Proof_A_subset_axes

set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof
namespace Erdos654Proof
theorem _root_.solution (m : ℕ) : NoFourConcyclic (A m : Set ℝ²) :=
  fun T hT ↦ noFourConcyclic_axes T (hT.trans (A_subset_axes m))
end Erdos654Proof
