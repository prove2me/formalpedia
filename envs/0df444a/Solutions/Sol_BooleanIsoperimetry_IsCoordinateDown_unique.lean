-- Prove2me | solution 1 for BooleanIsoperimetry.IsCoordinateDown_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:04.314411+00:00
-- url     : https://prove2.me/submissions/e4220139-bf9f-4198-a733-c7a630db22e5

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {i : Fin N} {A A' A'' : Finset (Cube N)}
    (h1 : IsCoordinateDown i A A') (h2 : IsCoordinateDown i A A'') : A' = A'' := by
  ext x
  rw [h1.2, h2.2]
end BooleanIsoperimetry
