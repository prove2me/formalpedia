-- Prove2me | solution 1 for CSeparatedNPComplete.sum_mul_nonneg_of_antitone_of_partial_sum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:46:10.132913+00:00
-- url     : https://prove2.me/submissions/0d818c9d-9abe-40b3-a08c-eca8fbc71abf

module
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Definitions.Def_CSeparatedNPComplete_WeightedSum

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
open scoped BigOperators
namespace CSeparatedNPComplete
theorem _root_.solution
    (n : ℕ) (a c : ℕ → ℝ)
    (hc : ∀ i, i + 1 < n → c (i + 1) ≤ c i)
    (ha : ∀ k, k ≤ n → 0 ≤ ∑ i ∈ Finset.range k, a i)
    (ht : ∑ i ∈ Finset.range n, a i = 0) :
    0 ≤ ∑ i ∈ Finset.range n, c i * a i := by
  have hab := Finset.sum_range_by_parts c a n
  simp only [smul_eq_mul, ht, mul_zero, zero_sub] at hab
  rw [hab]
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro i hi
  have hi' : i < n - 1 := Finset.mem_range.mp hi
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hc i (by omega)))
    (ha (i + 1) (by omega))
end CSeparatedNPComplete
