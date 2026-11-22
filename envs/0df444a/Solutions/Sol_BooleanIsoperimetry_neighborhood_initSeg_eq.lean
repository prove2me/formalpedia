-- Prove2me | solution 1 for BooleanIsoperimetry.neighborhood_initSeg_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:13.979473+00:00
-- url     : https://prove2.me/submissions/ca62a16e-5d05-4de7-9fe0-e8f7a2ea5bf5

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_rank_mono
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_initSeg_iff
public import Theorems.Thm_BooleanIsoperimetry_gShift_monotone
public import Theorems.Thm_BooleanIsoperimetry_downwardClosed_eq_initSeg

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k : ℕ} :
    neighborhood 1 (simplicialInitSeg n k) = simplicialInitSeg n (H n k) := by
  have hdc : ∀ x y, simplicialLe x y → y ∈ neighborhood 1 (simplicialInitSeg n k) →
      x ∈ neighborhood 1 (simplicialInitSeg n k) := by
    intro x y hxy hy
    rw [mem_neighborhood_initSeg_iff] at hy ⊢
    exact lt_of_le_of_lt (rank_mono (gShift_monotone hxy)) hy
  exact downwardClosed_eq_initSeg hdc
end BooleanIsoperimetry
