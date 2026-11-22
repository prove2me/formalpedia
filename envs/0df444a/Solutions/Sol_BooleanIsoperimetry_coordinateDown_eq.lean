-- Prove2me | solution 1 for BooleanIsoperimetry.coordinateDown_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:32.003818+00:00
-- url     : https://prove2.me/submissions/71b69f6d-3fbd-4943-ae0c-91b7b625ae58

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_coordinateDown_spec
public import Theorems.Thm_BooleanIsoperimetry_IsCoordinateDown_unique

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {i : Fin N} {A A' : Finset (Cube N)}
    (hA : IsCoordinateDown i A A') : A' = coordinateDown i A :=
  IsCoordinateDown_unique hA (coordinateDown_spec i A)
end BooleanIsoperimetry
