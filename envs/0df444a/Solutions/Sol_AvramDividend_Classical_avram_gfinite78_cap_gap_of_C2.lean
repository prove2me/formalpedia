-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite78_cap_gap_of_C2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:09:54.519654+00:00
-- url     : https://prove2.me/submissions/d93b55c4-f286-4d7d-b917-12f56bcbec1c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gfinite74_cap_gap_of_grad
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical

/-- Interior C² regularity supplies the differentiability assumption of
    the proved finite-cap derivative bound. -/
theorem solution
    (w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn w (Icc a b))
    (hsmooth : ContDiffOn ℝ 2 w (Ioo a b))
    (hgrad : ∀ z ∈ Ioo a b, 1 ≤ deriv w z) :
    0 ≤ (w b - w a) - (b - a) := by
  have hdiffOn : DifferentiableOn ℝ w (Ioo a b) :=
    hsmooth.differentiableOn (by norm_num)
  have hdiff : ∀ z ∈ Ioo a b, DifferentiableAt ℝ w z := by
    intro z hz
    exact (hdiffOn z hz).differentiableAt (isOpen_Ioo.mem_nhds hz)
  exact avram_gfinite74_cap_gap_of_grad w a b hab hcont hdiff hgrad
