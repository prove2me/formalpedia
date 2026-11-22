-- Prove2me | solution 1 for BooleanIsoperimetry.sum_pow_two_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:40:19.101807+00:00
-- url     : https://prove2.me/submissions/b20456e0-dfe5-4e4b-b56e-3213148d76a3

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ) : (∑ i ∈ Finset.range n, 2^i) < 2^n := by
  rw [Nat.geomSum_eq] <;> norm_num
end BooleanIsoperimetry
