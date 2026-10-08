-- Prove2me | solution 1 for AvramDividend.Classical.derivative_ge_one_implies_value_drop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:27:23.394308+00:00
-- url     : https://prove2.me/submissions/3a55def1-f2e5-4ed1-887d-ea440834e139

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution
    (w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn w (Icc a b))
    (hdiff : DifferentiableOn ℝ w (Ioo a b))
    (hgrad : ∀ z ∈ Ioo a b, 1 ≤ deriv w z) :
    b - a ≤ w b - w a := by
  have hdiff' : DifferentiableOn ℝ w (interior (Icc a b)) := by
    simpa only [interior_Icc] using hdiff
  have hgrad' : ∀ z ∈ interior (Icc a b),
      (1 : ℝ) ≤ deriv w z := by
    intro z hz
    exact hgrad z (by simpa only [interior_Icc] using hz)
  have h :=
    (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
      hcont hdiff' hgrad'
      a (left_mem_Icc.mpr hab)
      b (right_mem_Icc.mpr hab) hab
  simpa only [one_mul] using h
