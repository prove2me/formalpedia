-- Prove2me | solution 1 for Erdos657Proof.dist_pt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:24:54.392099+00:00
-- url     : https://prove2.me/submissions/e407213b-7164-40b4-ada4-2e9c09a2d012

module
public import Mathlib
public import Definitions.Def_Erdos657Palomar_Solution
public import Theorems.Thm_Erdos657Proof_w_sq
public import Theorems.Thm_Erdos657Proof_pt_apply

set_option autoImplicit true
@[expose] public section
public section
open scoped Finset
open Filter
open scoped EuclideanGeometry
open Erdos657Proof
open Finset
namespace Erdos657Proof
theorem _root_.solution {k : ℕ} (S T : Finset (Fin k)) :
    dist (pt S) (pt T) = Real.sqrt (g (symmDiff S T)) := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  have h : ∀ i, dist (pt S i) (pt T i) ^ 2 =
      if i ∈ symmDiff S T then (2 : ℝ) ^ (i : ℕ) else 0 := by
    intro i
    rw [Real.dist_eq, sq_abs, pt_apply, pt_apply]
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT, w_sq, Finset.mem_symmDiff]
  rw [sum_congr rfl fun i _ ↦ h i, sum_ite_mem, univ_inter, g]
end Erdos657Proof
