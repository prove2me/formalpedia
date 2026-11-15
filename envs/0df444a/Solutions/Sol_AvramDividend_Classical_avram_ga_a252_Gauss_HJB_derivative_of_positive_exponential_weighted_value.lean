-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a252_Gauss_HJB_derivative_of_positive_exponential_weighted_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:56:17.952203+00:00
-- url     : https://prove2.me/submissions/18f95d19-fe11-4267-9dc4-9e4295b67d71

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (f fp : ℝ → ℝ) (alpha y : ℝ)
    (hf : HasDerivAt f (fp y) y) :
    HasDerivAt (fun t => Real.exp (-alpha*t)*f t)
      (Real.exp (-alpha*y)*(fp y-alpha*f y)) y := by
  have hlin : HasDerivAt (fun t : ℝ => -alpha*t) (-alpha) y := by
    simpa using (hasDerivAt_id y).const_mul (-alpha)
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-alpha*t))
      (Real.exp (-alpha*y)*(-alpha)) y := by
    simpa only [mul_comm] using hlin.exp
  have hprod := hexp.mul hf
  have hEq : (Real.exp (-alpha*y)*(-alpha))*f y +
      Real.exp (-alpha*y)*fp y =
      Real.exp (-alpha*y)*(fp y-alpha*f y) := by ring
  rw [←hEq]
  exact hprod
