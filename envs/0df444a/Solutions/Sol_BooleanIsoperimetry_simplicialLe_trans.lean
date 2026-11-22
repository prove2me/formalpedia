-- Prove2me | solution 1 for BooleanIsoperimetry.simplicialLe_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:40:27.642104+00:00
-- url     : https://prove2.me/submissions/324fc581-219a-4d78-aaab-afa11a33e852

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
theorem _root_.solution {n : ℕ} (a b c : Cube n)
    (hab : simplicialLe a b) (hbc : simplicialLe b c) : simplicialLe a c := by
  unfold simplicialLe at *
  rcases hab with hab_lt | ⟨hab_eq, hab_nat⟩
  · rcases hbc with hbc_lt | ⟨hbc_eq, _⟩
    · left; omega
    · left; omega
  · rcases hbc with hbc_lt | ⟨hbc_eq, hbc_nat⟩
    · left; omega
    · right
      constructor
      · omega
      · exact le_trans hbc_nat hab_nat
end BooleanIsoperimetry
