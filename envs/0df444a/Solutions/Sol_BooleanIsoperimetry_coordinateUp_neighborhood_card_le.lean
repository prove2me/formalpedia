-- Prove2me | solution 1 for BooleanIsoperimetry.coordinateUp_neighborhood_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:33:02.770297+00:00
-- url     : https://prove2.me/submissions/f0fa9572-150d-4611-8d07-63939f41209e

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
public import Theorems.Thm_BooleanIsoperimetry_coordinateUp_eq
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_coordinateUp_subset
public import Theorems.Thm_BooleanIsoperimetry_coordinateUp_card_eq

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {i : Fin N} {A A' : Finset (Cube N)}
    (hA : IsCoordinateUp i A A') :
    (neighborhood 1 A').card ≤ (neighborhood 1 A).card := by
  rw [coordinateUp_eq hA]
  have h_sub := neighborhood_coordinateUp_subset (A := A) (i := i)
  have h_card := coordinateUp_card_eq (coordinateUp_spec i (neighborhood 1 A))
  exact le_trans (card_le_card h_sub) (le_of_eq h_card)
end BooleanIsoperimetry
