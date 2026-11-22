-- Prove2me | solution 1 for BooleanIsoperimetry.binomPrefix_pascal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:15:22.154512+00:00
-- url     : https://prove2.me/submissions/cdb38286-644b-48f3-a801-63abf14d55f4

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n r : ℕ) :
    binomPrefix (n + 1) r = binomPrefix n r + binomPrefix n (r - 1) := by
  simp +arith +decide only [binomPrefix]
  rcases r with (_ | r) <;> simp +arith +decide only [Finset.range_zero, Finset.sum_empty,
    zero_tsub, add_zero, Finset.sum_range_succ', Nat.choose_succ_succ, Nat.succ_eq_add_one,
    Nat.choose_zero_right, add_tsub_cancel_right]
  rw [Finset.sum_add_distrib]
end BooleanIsoperimetry
