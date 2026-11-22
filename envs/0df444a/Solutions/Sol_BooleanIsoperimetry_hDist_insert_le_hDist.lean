-- Prove2me | solution 1 for BooleanIsoperimetry.hDist_insert_le_hDist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:30.177108+00:00
-- url     : https://prove2.me/submissions/cab6fb03-7cf2-4b9c-8ada-bbc3d5f81108

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (i : Fin N) (x y : Cube N) (h : hDist x y ≤ 1) :
    hDist (insert i x) (insert i y) ≤ 1 := by
  unfold hDist at h ⊢
  have : symmDiff (insert i x) (insert i y) ⊆ symmDiff x y := by
    intro j hj
    simp only [mem_symmDiff, mem_insert] at hj ⊢
    tauto
  exact le_trans (card_le_card this) h
end BooleanIsoperimetry
