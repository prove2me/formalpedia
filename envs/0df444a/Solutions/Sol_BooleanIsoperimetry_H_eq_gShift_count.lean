-- Prove2me | solution 1 for BooleanIsoperimetry.H_eq_gShift_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:29:30.188837+00:00
-- url     : https://prove2.me/submissions/cd5ae2ed-7210-4e6d-94ef-fa71dceaf031

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_initSeg_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n k : ℕ) :
    H n k = (Finset.univ.filter (fun v : Cube n => rank (gShift v) < k)).card := by
  unfold H
  congr 1
  ext v
  rw [mem_neighborhood_initSeg_iff]
  simp
end BooleanIsoperimetry
