-- Prove2me | solution 1 for BooleanIsoperimetry.mem_neighborhood_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:14:33.000827+00:00
-- url     : https://prove2.me/submissions/d5f9eb25-4b71-4c42-8bd3-470eae7a03f2

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
theorem _root_.solution {n r : ℕ} {A : Finset (Cube n)} {v : Cube n} :
  v ∈ neighborhood r A ↔ ∃ u ∈ A, hDist u v ≤ r := by
  simp [neighborhood]
end BooleanIsoperimetry
