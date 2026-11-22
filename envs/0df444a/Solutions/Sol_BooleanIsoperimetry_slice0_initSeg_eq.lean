-- Prove2me | solution 1 for BooleanIsoperimetry.slice0_initSeg_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:31:15.877003+00:00
-- url     : https://prove2.me/submissions/af482e36-db5a-4396-9395-ff38acc104f2

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
public import Theorems.Thm_BooleanIsoperimetry_embed0_mono
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n k : ℕ} :
    slice0 (simplicialInitSeg (n + 1) k) =
      simplicialInitSeg n (slice0 (simplicialInitSeg (n + 1) k)).card := by
  apply downwardClosed_eq_initSeg; intro x y h_le h_mem; exact (by
  simp_all +decide only [simplicialInitSeg]
  simp_all +decide only [slice0, Finset.mem_filter, Finset.mem_univ, true_and]
  exact lt_of_le_of_lt (rank_mono (embed0_mono h_le) ) h_mem)
end BooleanIsoperimetry
