-- Prove2me | solution 1 for BooleanIsoperimetry.binomPrefix_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:18:19.916897+00:00
-- url     : https://prove2.me/submissions/69951603-8601-4371-9048-7a9691f01a94

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_mono
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_full
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n r : ℕ) : binomPrefix n r ≤ 2 ^ n := by
  by_cases hr : r ≤ n + 1
  · exact le_trans (binomPrefix_mono n hr) (by rw [binomPrefix_full])
  · rw [← binomPrefix_full]
    unfold binomPrefix
    rw [← Finset.sum_range_add_sum_Ico _ (by linarith : n + 1 ≤ r)]
    simp +zetaDelta only [not_le, add_le_iff_nonpos_right, nonpos_iff_eq_zero,
      Finset.sum_eq_zero_iff, Finset.mem_Ico, Order.add_one_le_iff, and_imp] at *
    exact fun i hi₁ hi₂ => Nat.choose_eq_zero_of_lt hi₁
end BooleanIsoperimetry
