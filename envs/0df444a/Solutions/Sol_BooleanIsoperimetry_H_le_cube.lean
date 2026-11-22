-- Prove2me | solution 1 for BooleanIsoperimetry.H_le_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:15:18.746462+00:00
-- url     : https://prove2.me/submissions/2cc56ef6-75a2-4b1a-b53b-db19c7742723

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n k : ℕ) : H n k ≤ 2 ^ n := by
  have h : (neighborhood 1 (simplicialInitSeg n k)).card ≤ Fintype.card (Cube n) :=
    Finset.card_le_univ _
  simpa [H, Cube, Fintype.card_finset] using h
end BooleanIsoperimetry
