-- Prove2me | solution 1 for BooleanIsoperimetry.coordinateDown_potential_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:42:05.505255+00:00
-- url     : https://prove2.me/submissions/2752518b-4e83-45a6-b4cc-fbdc3900a1b2

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_downMap_rank_le
public import Theorems.Thm_BooleanIsoperimetry_downMap_injOn
public import Theorems.Thm_BooleanIsoperimetry_coordinateDown_eq_image

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (i : Fin N) (A : Finset (Cube N)) :
    compressionPotential (coordinateDown i A) ≤ compressionPotential A := by
  unfold compressionPotential
  rw [coordinateDown_eq_image, Finset.sum_image (fun x hx y hy h => downMap_injOn i A hx hy h)]
  exact Finset.sum_le_sum (fun x _ => downMap_rank_le i A x)
end BooleanIsoperimetry
