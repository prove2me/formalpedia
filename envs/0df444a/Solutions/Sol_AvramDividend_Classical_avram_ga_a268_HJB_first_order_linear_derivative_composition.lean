-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a268_HJB_first_order_linear_derivative_composition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:05:37.717196+00:00
-- url     : https://prove2.me/submissions/d80f97fb-24c9-4934-9bb6-989cc40c4925

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (f fp : ℝ → ℝ) (fpp lambda y : ℝ)
    (hf : HasDerivAt f (fp y) y)
    (hfp : HasDerivAt fp fpp y) :
    HasDerivAt (fun t : ℝ => fp t-lambda*f t)
      (fpp-lambda*fp y) y := by
  exact hfp.sub (hf.const_mul lambda)
