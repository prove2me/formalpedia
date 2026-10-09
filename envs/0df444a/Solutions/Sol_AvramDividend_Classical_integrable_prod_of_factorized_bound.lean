-- Prove2me | solution 1 for AvramDividend.Classical.integrable_prod_of_factorized_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:17:26.345005+00:00
-- url     : https://prove2.me/submissions/8716e232-32ee-4b63-a3b7-a9fe4289403a

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

theorem solution
    (μ ν : Measure ℝ) (f : ℝ × ℝ → ℝ) (g h : ℝ → ℝ)
    (hg : Integrable g μ) (hh : Integrable h ν)
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hdom : ∀ᵐ p ∂(μ.prod ν), ‖f p‖ ≤ |g p.1| * |h p.2|) :
    Integrable f (μ.prod ν) := by
  have hprod : Integrable
      (fun p : ℝ × ℝ => |g p.1| * |h p.2|) (μ.prod ν) := by
    simpa only [Real.norm_eq_abs] using hg.norm.mul_prod hh.norm
  exact hprod.mono' hf hdom
