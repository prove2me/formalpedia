-- Prove2me | solution 1 for Erdos657Proof.pt_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:58:55.314132+00:00
-- url     : https://prove2.me/submissions/afa706be-bbaa-486f-8ea7-38b735adcbdb

module
public import Mathlib
public import Definitions.Def_Erdos657Palomar_Solution
public import Theorems.Thm_Erdos657Proof_symmDiff_eq_of_dist_eq

set_option autoImplicit true
@[expose] public section
public section
open scoped Finset
open Filter
open scoped EuclideanGeometry
open Erdos657Proof
open Finset
namespace Erdos657Proof
theorem _root_.solution (k : ℕ) : Function.Injective (pt (k := k)) := by
  intro S T h
  have h0 : symmDiff S T = symmDiff T T :=
    symmDiff_eq_of_dist_eq (by rw [h])
  rwa [symmDiff_self, symmDiff_eq_bot] at h0
end Erdos657Proof
