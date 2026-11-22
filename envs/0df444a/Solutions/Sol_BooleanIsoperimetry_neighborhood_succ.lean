-- Prove2me | solution 1 for BooleanIsoperimetry.neighborhood_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:22.473825+00:00
-- url     : https://prove2.me/submissions/3615efeb-09ec-4f8d-b7ac-14501d302575

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_slice_card_add
public import Theorems.Thm_BooleanIsoperimetry_slice0_neighborhood
public import Theorems.Thm_BooleanIsoperimetry_slice1_neighborhood

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (A : Finset (Cube (n + 1))) :
    (neighborhood 1 A).card =
    (neighborhood 1 (slice0 A) ∪ slice1 A).card +
    (neighborhood 1 (slice1 A) ∪ slice0 A).card := by
  rw [← slice_card_add, slice0_neighborhood, slice1_neighborhood]
end BooleanIsoperimetry
