-- Prove2me | solution 1 for BooleanIsoperimetry.coordinateUp_mem_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:04.765815+00:00
-- url     : https://prove2.me/submissions/81a2aa54-37d5-4572-ad4a-11f1f8c32b1b

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_mem_coordinateUp_iff
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (i : Fin N) (A : Finset (Cube N)) (x : Cube N)
    (hix : i ∉ x) : x ∈ coordinateUp i A ↔ x ∈ A ∧ insert i x ∈ A := by
  rw [mem_coordinateUp_iff]; simp [hix]
end BooleanIsoperimetry
