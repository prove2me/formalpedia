-- Prove2me | solution 1 for AvramDividend.Classical.monotone_nonzero_derivative_eventually_right_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:38:37.407035+00:00
-- url     : https://prove2.me/submissions/605c0b09-67e2-436e-ad06-acd97dbd2bd9

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Order.GroupWithZero.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set
open scoped Topology

theorem solution
    (W : ℝ → ℝ) (a : ℝ)
    (hmono : Monotone W)
    (hD : HasDerivAt W (deriv W a) a)
    (hd : deriv W a ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), W a < W (a + ε) := by
  have hn : 0 ≤ deriv W a := hD.nonneg_of_monotone hmono
  have hp : 0 < deriv W a := lt_of_le_of_ne hn hd.symm
  have hslope : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ε⁻¹ * (W (a + ε) - W a) :=
    hD.tendsto_slope_zero_right.eventually (eventually_gt_nhds hp)
  have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := by
    change Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)
    exact self_mem_nhdsWithin
  filter_upwards [hslope, hε] with ε hmul heps
  have hinv : 0 < ε⁻¹ := inv_pos.mpr heps
  have hmul' : 0 < (W (a + ε) - W a) * ε⁻¹ := by
    simpa only [mul_comm] using hmul
  exact sub_pos.mp (pos_of_mul_pos_left hmul' (le_of_lt hinv))
