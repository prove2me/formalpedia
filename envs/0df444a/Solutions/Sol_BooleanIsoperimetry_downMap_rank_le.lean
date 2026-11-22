-- Prove2me | solution 1 for BooleanIsoperimetry.downMap_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:24:23.553117+00:00
-- url     : https://prove2.me/submissions/d20e7ef8-f0b8-4024-b01d-6396ac8b27eb

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_simplicialLt_erase_self
public import Theorems.Thm_BooleanIsoperimetry_rank_strictMono


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (i : Fin N) (A : Finset (Cube N)) (x : Cube N) :
    rank (downMap i A x) ≤ rank x := by
  unfold downMap
  split
  · next h => exact le_of_lt (rank_strictMono (simplicialLt_erase_self h.1))
  · exact le_rfl
end BooleanIsoperimetry
