-- Prove2me | solution 1 for BooleanIsoperimetry.initSeg_nested
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:15:21.138309+00:00
-- url     : https://prove2.me/submissions/3a4a0130-46d2-47d8-b38a-163011f4a00a

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} {k m : ℕ} (h : k ≤ m) :
    simplicialInitSeg n k ⊆ simplicialInitSeg n m := by
  intro x hx
  simp only [simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact Nat.lt_of_lt_of_le hx h
end BooleanIsoperimetry
