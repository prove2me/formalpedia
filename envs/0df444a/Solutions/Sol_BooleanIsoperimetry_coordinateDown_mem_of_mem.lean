-- Prove2me | solution 1 for BooleanIsoperimetry.coordinateDown_mem_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:08.04708+00:00
-- url     : https://prove2.me/submissions/2a70fda8-3be0-417a-8c43-c4c3b9bba98f

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_mem_coordinateDown_iff
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (i : Fin N) (B : Finset (Cube N)) (x : Cube N)
    (hix : i ∈ x) : x ∈ coordinateDown i B ↔ x ∈ B ∧ x.erase i ∈ B := by
  rw [mem_coordinateDown_iff]; simp [hix]
end BooleanIsoperimetry
