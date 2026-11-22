-- Prove2me | solution 1 for BooleanIsoperimetry.mem_coordinateUp_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:21.048317+00:00
-- url     : https://prove2.me/submissions/c7350c8e-e678-4e8d-8fa1-408daf320041

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_coordinateUp_spec

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (i : Fin N) (A : Finset (Cube N)) (x : Cube N) :
    x ∈ coordinateUp i A ↔
      (x ∈ A ∧ (i ∈ x ∨ insert i x ∈ A)) ∨ (i ∈ x ∧ x ∉ A ∧ x.erase i ∈ A) :=
  (coordinateUp_spec i A).2 x
end BooleanIsoperimetry
