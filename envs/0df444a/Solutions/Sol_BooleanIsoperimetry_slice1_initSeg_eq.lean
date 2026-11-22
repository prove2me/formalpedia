-- Prove2me | solution 1 for BooleanIsoperimetry.slice1_initSeg_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:14.600071+00:00
-- url     : https://prove2.me/submissions/c744b8fd-d248-4a1f-96c8-cb5884e5bd01

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_rank_mono
public import Theorems.Thm_BooleanIsoperimetry_downwardClosed_eq_initSeg
public import Theorems.Thm_BooleanIsoperimetry_embed1_mono
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k : ℕ} :
    slice1 (simplicialInitSeg (n + 1) k) =
      simplicialInitSeg n (slice1 (simplicialInitSeg (n + 1) k)).card := by
  apply downwardClosed_eq_initSeg
  intro x y hxy hy
  simp_all +decide only [slice1, simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and]
  refine lt_of_le_of_lt ?_ hy
  apply rank_mono; exact embed1_mono hxy
end BooleanIsoperimetry
