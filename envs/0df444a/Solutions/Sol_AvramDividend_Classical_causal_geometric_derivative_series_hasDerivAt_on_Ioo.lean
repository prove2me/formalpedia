-- Prove2me | solution 1 for AvramDividend.Classical.causal_geometric_derivative_series_hasDerivAt_on_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:02:14.991134+00:00
-- url     : https://prove2.me/submissions/6763dce2-5133-4146-bc9f-8861613e5b60

import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- A local geometric majorant permits term-by-term differentiation of a series. -/
theorem solution
    (g g' : ℕ → ℝ → ℝ) (a b C r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hg : ∀ n y, y ∈ Ioo a b → HasDerivAt (g n) (g' n y) y)
    (hbound : ∀ n y, y ∈ Ioo a b → ‖g' n y‖ ≤ C * r ^ n)
    (y₀ : ℝ) (hy₀ : y₀ ∈ Ioo a b)
    (hval : Summable fun n => g n y₀)
    (y : ℝ) (hy : y ∈ Ioo a b) :
    HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n y) y := by
  have hrabs : |r| < 1 := by
    simpa only [abs_of_nonneg hr0] using hr1
  have hu : Summable (fun n : ℕ => C * r ^ n) :=
    (summable_geometric_of_abs_lt_one hrabs).mul_left C
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
    isPreconnected_Ioo hg hbound hy₀ hval hy
