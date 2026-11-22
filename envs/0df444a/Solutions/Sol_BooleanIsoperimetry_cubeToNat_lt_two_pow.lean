-- Prove2me | solution 1 for BooleanIsoperimetry.cubeToNat_lt_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:41.738361+00:00
-- url     : https://prove2.me/submissions/ab5e3620-59a5-4e37-b8ad-62adb976fae0

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
theorem _root_.solution {n M : ℕ} {x : Cube n} (h : ∀ i ∈ x, (i : ℕ) < M) :
    cubeToNat x < 2 ^ M := by
  -- The sum of the powers of 2 in x is bounded by the sum of the powers of 2 up to M-1.
  have h_sum_bound : ∑ i ∈ x, 2 ^ (i : ℕ) ≤ ∑ j ∈ Finset.range M, 2 ^ j := by
    exact le_trans
      (by
        rw [← Finset.sum_image (by
          intros a ha b hb hab
          exact Fin.ext <| by simpa using hab)])
      (Finset.sum_le_sum_of_subset <|
        Finset.image_subset_iff.mpr fun i hi => Finset.mem_range.mpr <| h i hi)
  generalize_proofs at *; (
  exact lt_of_le_of_lt h_sum_bound (Nat.geomSum_lt (by norm_num) (by aesop) ))
end BooleanIsoperimetry
