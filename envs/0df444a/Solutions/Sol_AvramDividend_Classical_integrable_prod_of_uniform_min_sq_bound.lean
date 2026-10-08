-- Prove2me | solution 1 for AvramDividend.Classical.integrable_prod_of_uniform_min_sq_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:43:18.058612+00:00
-- url     : https://prove2.me/submissions/27d067be-2bc1-4cc0-9649-359bfe82d25f

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    (hmoment : Integrable (fun y : ℝ => min 1 (y ^ 2)) ν)
    (f : ℝ × ℝ → ℝ)
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ p : ℝ × ℝ, ‖f p‖ ≤ C * min 1 (p.2 ^ 2)) :
    Integrable f (μ.prod ν) := by
  have hconst : Integrable (fun _ : ℝ => C) μ :=
    integrable_const C
  have hprod : Integrable
      (fun p : ℝ × ℝ => C * min 1 (p.2 ^ 2))
      (μ.prod ν) := hconst.mul_prod hmoment
  apply hprod.mono' hf
  filter_upwards [] with p
  have hmin : 0 ≤ min (1 : ℝ) (p.2 ^ 2) :=
    le_min (by norm_num) (sq_nonneg _)
  have hpos : 0 ≤ C * min 1 (p.2 ^ 2) :=
    mul_nonneg hC hmin
  simpa only [Real.norm_eq_abs, abs_of_nonneg hpos] using hbound p
