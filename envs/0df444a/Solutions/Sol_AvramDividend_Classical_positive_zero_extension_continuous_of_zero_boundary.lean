-- Prove2me | solution 1 for AvramDividend.Classical.positive_zero_extension_continuous_of_zero_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T06:52:43.973342+00:00
-- url     : https://prove2.me/submissions/21c166d3-b54d-428c-8464-0001b745d9ae

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Order.DenselyOrdered

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- A continuous positive-time function with zero boundary value extends by zero. -/
theorem solution
    (g : ℝ → ℝ)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hg0 : g 0 = 0) :
    Continuous ((Ioi (0 : ℝ)).indicator g) := by
  apply continuous_indicator
  · intro x hx
    have hzero : x = 0 := by
      simpa only [frontier_Ioi, mem_singleton_iff] using hx
    simpa only [hzero] using hg0
  · simpa only [closure_Ioi] using hg
