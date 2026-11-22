-- Prove2me | solution 1 for BooleanIsoperimetry.exists_downMap_ne_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:58.755385+00:00
-- url     : https://prove2.me/submissions/3754d516-e054-4c7d-82bc-01b6b7246552

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_coordinateDown_eq_image

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (i : Fin N) (A : Finset (Cube N))
    (hne : coordinateDown i A ≠ A) : ∃ x ∈ A, downMap i A x ≠ x := by
  by_contra hcon
  push Not at hcon
  apply hne
  rw [coordinateDown_eq_image, Finset.image_congr (g := id) (fun x hx => hcon x hx),
    Finset.image_id]
end BooleanIsoperimetry
