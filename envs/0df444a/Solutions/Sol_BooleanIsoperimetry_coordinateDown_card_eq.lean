-- Prove2me | solution 1 for BooleanIsoperimetry.coordinateDown_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:23:45.058514+00:00
-- url     : https://prove2.me/submissions/2dcee55a-ea9c-46c0-9e2f-775a9ad86b4a

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
theorem _root_.solution {N : ℕ} {i : Fin N} {B B' : Finset (Cube N)}
    (hB : IsCoordinateDown i B B') :
    B'.card = B.card :=
  hB.1
end BooleanIsoperimetry
