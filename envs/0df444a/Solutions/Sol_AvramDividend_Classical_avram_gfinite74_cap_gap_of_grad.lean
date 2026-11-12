-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite74_cap_gap_of_grad
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:47:18.221214+00:00
-- url     : https://prove2.me/submissions/54105313-8124-40b0-870c-0cc431e23932

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gfinite72_cap_gap_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_gfinite73_excess_mono_of_deriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- The finite-cap corner slack is nonnegative whenever the dividend
    value has marginal value at least one on the cap strip. -/
theorem solution
    (w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn w (Icc a b))
    (hdiff : ∀ z ∈ Ioo a b, DifferentiableAt ℝ w z)
    (hgrad : ∀ z ∈ Ioo a b, 1 ≤ deriv w z) :
    0 ≤ (w b - w a) - (b - a) := by
  exact AvramDividend.Classical.avram_gfinite72_cap_gap_nonnegative
    w a b hab
    (AvramDividend.Classical.avram_gfinite73_excess_mono_of_deriv
      w a b hcont hdiff hgrad)
