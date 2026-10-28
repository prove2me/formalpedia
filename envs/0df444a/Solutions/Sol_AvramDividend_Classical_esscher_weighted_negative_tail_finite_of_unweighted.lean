-- Prove2me | solution 1 for AvramDividend.Classical.esscher_weighted_negative_tail_finite_of_unweighted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:07:19.953906+00:00
-- url     : https://prove2.me/submissions/659d5d5c-4ec2-4ec1-b42a-5993aa8a34c1

import Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_le_unweighted
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution
    (ν : Measure ℝ) (φ x : ℝ) (hφ : 0 ≤ φ) (hx : 0 < x)
    (hfinite : ν (Iio (-x)) < ⊤) :
    (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
      (Iio (-x)) < ⊤ := by
  exact lt_of_le_of_lt
    (esscher_weighted_negative_tail_le_unweighted ν φ x hφ hx)
    hfinite
