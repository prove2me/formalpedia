-- Prove2me | solution 1 for Erdos657Proof.isIsoscelesFree_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:04:40.280965+00:00
-- url     : https://prove2.me/submissions/3854aaff-5c0d-4909-af5c-91f1b188a72b

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
theorem _root_.solution (k : ℕ) : ((univ.image pt : Finset (ℝ^k)) : Set (ℝ^k)).IsIsoscelesFree := by
  unfold Set.IsIsoscelesFree Set.Triplewise
  intro x hx y hy z hz hxy hyz hxz hiso
  simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at hx hy hz
  obtain ⟨S, rfl⟩ := hx
  obtain ⟨T, rfl⟩ := hy
  obtain ⟨U, rfl⟩ := hz
  unfold IsIsosceles at hiso
  rcases hiso with h | h | h
  · have := symmDiff_eq_of_dist_eq h
    rw [symmDiff_comm T U, symmDiff_left_inj] at this
    exact hxz (congrArg pt this)
  · have := symmDiff_eq_of_dist_eq h
    rw [symmDiff_comm T U, symmDiff_right_inj] at this
    exact hxy (congrArg pt this.symm)
  · have := symmDiff_eq_of_dist_eq h
    rw [symmDiff_comm U S, symmDiff_right_inj] at this
    exact hyz (congrArg pt this.symm)
end Erdos657Proof
