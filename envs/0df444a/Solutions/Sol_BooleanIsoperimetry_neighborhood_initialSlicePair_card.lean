-- Prove2me | solution 1 for BooleanIsoperimetry.neighborhood_initialSlicePair_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:16.110128+00:00
-- url     : https://prove2.me/submissions/45cb7407-5b91-4c4d-b028-76564baf3148

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_slice0_initialSlicePair
public import Theorems.Thm_BooleanIsoperimetry_slice1_initialSlicePair
public import Theorems.Thm_BooleanIsoperimetry_H_le_cube
public import Theorems.Thm_BooleanIsoperimetry_card_initSeg_union
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_initSeg_eq
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_succ


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N a b : ℕ}
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) :
    (neighborhood 1 (initialSlicePair N a b)).card =
      max (H N a) b + max (H N b) a := by
  rw [neighborhood_succ, slice0_initialSlicePair, slice1_initialSlicePair]
  rw [neighborhood_initSeg_eq, neighborhood_initSeg_eq]
  rw [card_initSeg_union (H_le_cube N a) hb, card_initSeg_union (H_le_cube N b) ha]
end BooleanIsoperimetry
