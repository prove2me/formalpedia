-- Prove2me | solution 1 for BooleanIsoperimetry.coordinateUp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:31.545101+00:00
-- url     : https://prove2.me/submissions/66e4b5ce-ec5c-4b0b-80fe-92852f0520d8

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
public import Theorems.Thm_BooleanIsoperimetry_IsCoordinateUp_unique

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {i : Fin N} {A A' : Finset (Cube N)}
    (hA : IsCoordinateUp i A A') : A' = coordinateUp i A :=
  IsCoordinateUp_unique hA (coordinateUp_spec i A)
end BooleanIsoperimetry
