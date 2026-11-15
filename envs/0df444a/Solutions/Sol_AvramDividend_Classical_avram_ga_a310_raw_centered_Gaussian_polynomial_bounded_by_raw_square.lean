-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a310_raw_centered_Gaussian_polynomial_bounded_by_raw_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:50:32.474463+00:00
-- url     : https://prove2.me/submissions/180e132a-e21a-4df1-a8b3-04190d91ded2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (r a : ℝ) :
    1 + |r| + (r-a)^2/2 ≤ 2*r^2 + a^2 + 2 := by
  have h0 : (|r|)^2 = r^2 := sq_abs r
  have h1 : 2*|r| ≤ r^2+1 := by
    nlinarith [sq_nonneg (|r|-1)]
  have h2 : (r-a)^2 ≤ 2*r^2+2*a^2 := by
    nlinarith [sq_nonneg (r+a)]
  nlinarith
