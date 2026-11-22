-- Prove2me | solution 1 for BooleanIsoperimetry.cubeToNat_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:18:12.491807+00:00
-- url     : https://prove2.me/submissions/c7c13e82-598b-49b2-acba-bc21a9041454

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
theorem _root_.solution {n : ℕ} {x : Cube n} {a : Fin n} (ha : a ∈ x) :
    cubeToNat x = cubeToNat (x.erase a) + 2 ^ (a : ℕ) := by
  unfold cubeToNat; rw [← Finset.sum_erase_add _ _ ha]
end BooleanIsoperimetry
