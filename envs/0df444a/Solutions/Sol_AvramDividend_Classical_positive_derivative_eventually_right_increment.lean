-- Prove2me | solution 1 for AvramDividend.Classical.positive_derivative_eventually_right_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:37:48.08872+00:00
-- url     : https://prove2.me/submissions/7ea6e063-283b-4a80-a602-9e1aee7f510e

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Order.GroupWithZero.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set
open scoped Topology

theorem solution
    (W : ℝ → ℝ) (a d : ℝ)
    (hD : HasDerivAt W d a) (hd : 0 < d) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), W a < W (a + ε) := by
  have hslope : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ε⁻¹ * (W (a + ε) - W a) :=
    hD.tendsto_slope_zero_right.eventually (eventually_gt_nhds hd)
  have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := by
    change Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)
    exact self_mem_nhdsWithin
  filter_upwards [hslope, hε] with ε hmul heps
  have hinv : 0 < ε⁻¹ := inv_pos.mpr heps
  have hmul' : 0 < (W (a + ε) - W a) * ε⁻¹ := by
    simpa only [mul_comm] using hmul
  exact sub_pos.mp (pos_of_mul_pos_left hmul' (le_of_lt hinv))
