-- Prove2me | solution 1 for BooleanIsoperimetry.rank_image_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:49.886385+00:00
-- url     : https://prove2.me/submissions/fe169b4f-4437-4e05-bcff-8bee4e32a0a8

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_rank_lt_two_pow
public import Theorems.Thm_BooleanIsoperimetry_rank_injective
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} :
    Finset.univ.image (@rank n) = Finset.range (2 ^ n) := by
  fapply Finset.eq_of_subset_of_card_le
  · exact Finset.image_subset_iff.mpr fun x _ => Finset.mem_range.mpr (rank_lt_two_pow x)
  · rw [Finset.card_image_of_injective _ rank_injective]; simp +decide [Finset.card_univ]
end BooleanIsoperimetry
