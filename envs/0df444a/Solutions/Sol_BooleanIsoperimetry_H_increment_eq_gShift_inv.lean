-- Prove2me | solution 1 for BooleanIsoperimetry.H_increment_eq_gShift_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:45.031918+00:00
-- url     : https://prove2.me/submissions/67c25312-2de0-46cf-b1d4-6ed282c96ee8

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_H_eq_gShift_count
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_rank_injective
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n p : ℕ) (w : Cube n) (hw : rank w = p) :
    H n (p + 1) =
      H n p + (Finset.filter (fun v => gShift v = w) (Finset.univ : Finset (Cube n))).card := by
  rw [H_eq_gShift_count n (p + 1), H_eq_gShift_count n p]
  have h_split : Finset.filter (fun v : Cube n => rank (gShift v) < p + 1) Finset.univ =
      Finset.filter (fun v : Cube n => rank (gShift v) < p) Finset.univ ∪
      Finset.filter (fun v : Cube n => rank (gShift v) = p) Finset.univ := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  rw [h_split]
  have h_disjoint : Disjoint (Finset.filter (fun v : Cube n => rank (gShift v) < p) Finset.univ)
      (Finset.filter (fun v : Cube n => rank (gShift v) = p) Finset.univ) := by
    rw [Finset.disjoint_filter]
    simp only [Finset.mem_univ, true_implies]
    intro v
    omega
  rw [Finset.card_union_of_disjoint h_disjoint]
  congr 1
  apply congr_arg
  apply Finset.filter_congr
  intro v _
  constructor
  · intro h
    have hr : rank (gShift v) = rank w := by rw [h, hw]
    exact rank_injective hr
  · intro h
    rw [h, hw]
end BooleanIsoperimetry
