-- Prove2me | solution 1 for AvramDividend.Classical.bv_positive_real_actual_quotient_formula_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:32:28.619375+00:00
-- url     : https://prove2.me/submissions/495eb514-2246-4d87-a58b-c4195dc90337

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

theorem solution
    (d : ℝ) (Z : ℝ≥0 → ℝ) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    (((d * (Real.toNNReal (t + ((1 : ℝ) / 2) ^ n) : ℝ) -
        Z (Real.toNNReal (t + ((1 : ℝ) / 2) ^ n))) -
      (d * (Real.toNNReal t : ℝ) - Z (Real.toNNReal t))) /
        ((1 : ℝ) / 2) ^ n) =
      d - (Z (Real.toNNReal t + ((1 : ℝ≥0) / 2) ^ n) -
        Z (Real.toNNReal t)) /
          (((1 : ℝ≥0) / 2) ^ n : ℝ) := by
  let δ : ℝ≥0 := ((1 : ℝ≥0) / 2) ^ n
  have hδ : (δ : ℝ) = ((1 : ℝ) / 2) ^ n := by
    simp [δ, NNReal.coe_pow, NNReal.coe_div]
  have hδpos : 0 < (δ : ℝ) := by
    rw [hδ]
    positivity
  have hShift :
      Real.toNNReal (t + ((1 : ℝ) / 2) ^ n) =
        Real.toNNReal t + δ := by
    apply NNReal.eq
    have hStep : 0 ≤ ((1 : ℝ) / 2) ^ n := by positivity
    have hSum : 0 ≤ t + ((1 : ℝ) / 2) ^ n :=
      add_nonneg ht hStep
    simpa [δ, NNReal.coe_add, NNReal.coe_pow, NNReal.coe_div] using
      (show ((Real.toNNReal (t + ((1 : ℝ) / 2) ^ n) : ℝ) =
        ((Real.toNNReal t : ℝ) + (δ : ℝ))) from by
          rw [Real.coe_toNNReal _ hSum, Real.coe_toNNReal _ ht]
          simp [hδ])
  rw [hShift, ← hδ]
  rw [NNReal.coe_add]
  change
    ((d * ((Real.toNNReal t : ℝ) + (δ : ℝ)) -
        Z (Real.toNNReal t + δ)) -
      (d * (Real.toNNReal t : ℝ) - Z (Real.toNNReal t))) /
        (δ : ℝ) =
      d - (Z (Real.toNNReal t + δ) - Z (Real.toNNReal t)) /
        (δ : ℝ)
  field_simp [ne_of_gt hδpos]
  ring
