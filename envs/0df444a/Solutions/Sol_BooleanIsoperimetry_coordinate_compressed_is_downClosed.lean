-- Prove2me | solution 1 for BooleanIsoperimetry.coordinate_compressed_is_downClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:42:07.34675+00:00
-- url     : https://prove2.me/submissions/8a5b878a-80a0-484d-9ee2-bbf105e50112

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_lowerLevelSaturated_colexFixed_is_downClosed

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (A : Finset (Cube N))
    (_hDown : IsCoordinateDownFixed A)
    (hLower : IsLowerLevelSaturated A)
    (hColex : IsColexShiftFixed A) :
    ∀ x y, simplicialLe x y → y ∈ A → x ∈ A :=
  lowerLevelSaturated_colexFixed_is_downClosed A hLower hColex
end BooleanIsoperimetry
