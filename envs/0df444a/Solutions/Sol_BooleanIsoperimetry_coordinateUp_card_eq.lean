-- Prove2me | solution 1 for BooleanIsoperimetry.coordinateUp_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:54.276184+00:00
-- url     : https://prove2.me/submissions/7979421c-ac75-4bb1-9b4c-95b40d1f3154

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
theorem _root_.solution {N : ℕ} {i : Fin N} {A A' : Finset (Cube N)}
    (hA : IsCoordinateUp i A A') :
    A'.card = A.card :=
  hA.1
end BooleanIsoperimetry
