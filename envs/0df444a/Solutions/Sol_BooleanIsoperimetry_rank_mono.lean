-- Prove2me | solution 1 for BooleanIsoperimetry.rank_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:14.195691+00:00
-- url     : https://prove2.me/submissions/99797951-4688-4833-ad4d-4d06535816f7

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_simplicialLe_antisymm
public import Theorems.Thm_BooleanIsoperimetry_rank_strictMono

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} {a b : Cube n} (h : simplicialLe a b) : rank a ≤ rank b := by
  by_cases hab : a = b
  · rw [hab]
  · -- If `a ≠ b`, antisymmetry turns `simplicialLe a b` into strict order.
    have h_lt : simplicialLt a b := by
      exact ⟨ h, fun h' => hab <| simplicialLe_antisymm _ _ h h' ⟩
    exact le_of_lt (rank_strictMono h_lt)
end BooleanIsoperimetry
