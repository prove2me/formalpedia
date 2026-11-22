-- Prove2me | solution 1 for BooleanIsoperimetry.hDist_self_insert_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:28.052007+00:00
-- url     : https://prove2.me/submissions/1fa59b5c-65a1-4dca-ab0a-2b6fd63607bd

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_hDist_comm
public import Theorems.Thm_BooleanIsoperimetry_hDist_insert_self_le_one

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (i : Fin N) (x : Cube N) : hDist x (insert i x) ≤ 1 := by
  rw [hDist_comm]; exact hDist_insert_self_le_one i x
end BooleanIsoperimetry
