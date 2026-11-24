-- Prove2me | solution 2 for FockRaiseLowGrade.eq_zero_of_hc
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T04:36:59.5678+00:00
-- url     : https://prove2.me/submissions/933f2dcf-c7fa-42f0-9641-a14ecde1d6a9

import Mathlib
open MvPolynomial
variable {σ : Type*}


theorem solution (x : MvPolynomial σ ℂ) (h : ∀ e, homogeneousComponent e x = 0) :
    x = 0 := by
  ext d; have H := congrArg (coeff d) (h (Finsupp.degree d)); simpa [coeff_homogeneousComponent] using H
