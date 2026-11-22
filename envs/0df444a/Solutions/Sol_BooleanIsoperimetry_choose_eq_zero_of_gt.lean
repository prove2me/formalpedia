-- Prove2me | solution 1 for BooleanIsoperimetry.choose_eq_zero_of_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:18.027813+00:00
-- url     : https://prove2.me/submissions/6a859db4-6846-42ff-abfb-b1dfc8e3db1c

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n r : ℕ} (h : n < r) : Nat.choose n r = 0 := by
  exact Nat.choose_eq_zero_of_lt h
end BooleanIsoperimetry
