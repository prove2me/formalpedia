-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_finite_mark_product_deleted_factor_sum_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:39:39.136924+00:00
-- url     : https://prove2.me/submissions/c5ab8456-1b61-4d38-874b-b5b7e2202176

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped BigOperators
noncomputable section

/-- The finite physical marked product satisfies the deleted-mark Mecke counting identity. -/
theorem solution {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℝ) :
    (∑ x ∈ S, f x * ∏ y ∈ S.erase x, f y) =
      (S.card : ℝ) * ∏ y ∈ S, f y := by
  classical
  calc
    _ = ∑ x ∈ S, ∏ y ∈ S, f y := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.mul_prod_erase S f hx
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
