-- Prove2me | solution 1 for BooleanIsoperimetry.coordinateDown_neighborhood_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:19.675187+00:00
-- url     : https://prove2.me/submissions/532b61d4-51b0-4929-ac08-345e85d5d022

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
public import Theorems.Thm_BooleanIsoperimetry_coordinateDown_eq
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_coordinateDown_subset
public import Theorems.Thm_BooleanIsoperimetry_coordinateDown_card_eq

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {i : Fin N} {B B' : Finset (Cube N)}
    (hB : IsCoordinateDown i B B') :
    (neighborhood 1 B').card ≤ (neighborhood 1 B).card := by
  rw [coordinateDown_eq hB]
  have h_sub := neighborhood_coordinateDown_subset (A := B) (i := i)
  have h_card := coordinateDown_card_eq (coordinateDown_spec i (neighborhood 1 B))
  exact le_trans (card_le_card h_sub) (le_of_eq h_card)
end BooleanIsoperimetry
