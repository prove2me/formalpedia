-- Prove2me | solution 1 for BooleanIsoperimetry.IsCoordinateUp_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:03.709548+00:00
-- url     : https://prove2.me/submissions/5178e32f-7653-4ae4-93ae-fb504d9dd18f

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
    (h1 : IsCoordinateUp i A A') (h2 : IsCoordinateUp i A A'') : A' = A'' := by
  ext x
  rw [h1.2, h2.2]
end BooleanIsoperimetry
