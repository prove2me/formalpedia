-- Prove2me | solution 1 for BooleanIsoperimetry.simplicialLe_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:40:23.754211+00:00
-- url     : https://prove2.me/submissions/4289e044-6d08-4825-bf37-b50939a8de68

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
theorem _root_.solution {n : ℕ} (a : Cube n) : simplicialLe a a := by
  unfold simplicialLe
  right
  exact ⟨rfl, le_rfl⟩
end BooleanIsoperimetry
