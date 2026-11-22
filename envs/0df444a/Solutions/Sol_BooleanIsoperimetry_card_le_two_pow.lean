-- Prove2me | solution 1 for BooleanIsoperimetry.card_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:15:25.626803+00:00
-- url     : https://prove2.me/submissions/3a301968-304c-47d0-b379-6301a63cf50d

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (S : Finset (Cube N)) : S.card ≤ 2 ^ N := by
  have h1 : S.card ≤ Fintype.card (Cube N) := Finset.card_le_univ S
  have h2 : Fintype.card (Cube N) = 2 ^ N := by
    simp [Cube, Fintype.card_finset, Fintype.card_fin]
  omega
end BooleanIsoperimetry
