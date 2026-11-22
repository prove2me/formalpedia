-- Prove2me | solution 1 for BooleanIsoperimetry.coordinateUp_mem_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:05.251792+00:00
-- url     : https://prove2.me/submissions/3dbb2974-eab8-440f-a0a0-8a0d4a2a039d

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
    (hix : i ∈ x) : x ∈ coordinateUp i A ↔ x ∈ A ∨ x.erase i ∈ A := by
  rw [mem_coordinateUp_iff]; simp [hix]; tauto
end BooleanIsoperimetry
