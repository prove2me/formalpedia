-- Prove2me | solution 1 for BooleanIsoperimetry.rank_lt_of_mem_simplicialInitSeg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:07.645836+00:00
-- url     : https://prove2.me/submissions/b9089f17-c4b3-43f5-bce0-1ce640015197

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
theorem _root_.solution {n : ℕ} {k : ℕ} {x : Cube n}
    (hx : x ∈ simplicialInitSeg n k) :
    rank x < k := by
  classical
  unfold simplicialInitSeg at hx
  exact Finset.mem_filter.mp hx |>.2
end BooleanIsoperimetry
