-- Prove2me | solution 1 for BooleanIsoperimetry.H_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:24.170689+00:00
-- url     : https://prove2.me/submissions/1e9d0da6-8ab9-4662-8456-bbad5bd8bee2

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_H_le_cube
public import Theorems.Thm_BooleanIsoperimetry_H_ge_self

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ) : H n (2 ^ n) = 2 ^ n := by
  exact le_antisymm (H_le_cube n (2 ^ n)) (H_ge_self n (2 ^ n) (le_rfl))
end BooleanIsoperimetry
