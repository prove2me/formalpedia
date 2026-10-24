-- Prove2me | solution 1 for AvramDividend.Classical.hasDerivAt_pos_eventually_forward_scale_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:15:24.436299+00:00
-- url     : https://prove2.me/submissions/35ddd823-d7ba-462c-9fe4-464393517f02

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Order.GroupWithZero.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

/-! A strictly positive derivative forces the forward scale increment to be positive nearby. -/
theorem solution
    (W : ℝ → ℝ) (a d : ℝ)
    (hD : HasDerivAt W d a) (hd : 0 < d) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < W (a + ε) - W a := by
  have hlim : Tendsto
      (fun ε : ℝ => ε⁻¹ * (W (a + ε) - W a))
      (𝓝[>] (0 : ℝ)) (𝓝 d) := by
    simpa only [smul_eq_mul] using hD.tendsto_slope_zero_right
  have hquot := Filter.Tendsto.eventually_const_lt hd hlim
  filter_upwards [hquot, self_mem_nhdsWithin] with ε hq hε
  exact pos_of_mul_pos_right hq (le_of_lt (inv_pos.mpr hε))
