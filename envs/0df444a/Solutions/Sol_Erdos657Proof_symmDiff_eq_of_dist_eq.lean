-- Prove2me | solution 1 for Erdos657Proof.symmDiff_eq_of_dist_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:52:36.052859+00:00
-- url     : https://prove2.me/submissions/c9d6933c-fe46-49ab-b3a2-d17c2b671772

module
public import Mathlib
public import Definitions.Def_Erdos657Palomar_Solution
public import Theorems.Thm_Erdos657Proof_g_nonneg
public import Theorems.Thm_Erdos657Proof_g_injective
public import Theorems.Thm_Erdos657Proof_dist_pt

set_option autoImplicit true
@[expose] public section
public section
open scoped Finset
open Filter
open scoped EuclideanGeometry
open Erdos657Proof
open Finset
namespace Erdos657Proof
theorem _root_.solution {k : ℕ} {S T U V : Finset (Fin k)}
    (h : dist (pt S) (pt T) = dist (pt U) (pt V)) : symmDiff S T = symmDiff U V := by
  rw [dist_pt, dist_pt] at h
  exact g_injective k ((Real.sqrt_inj (g_nonneg _) (g_nonneg _)).1 h)
end Erdos657Proof
