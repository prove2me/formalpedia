-- Prove2me | solution 1 for AvramDividend.Classical.hasDerivAt_pos_eventually_backward_scale_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:40:17.801346+00:00
-- url     : https://prove2.me/submissions/a6769eb7-e61b-4287-a5e3-290b7b0cc88a

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

/-! A positive derivative yields a positive backward scale difference near zero. -/
theorem solution
    (W : ℝ → ℝ) (a d : ℝ)
    (hD : HasDerivAt W d a) (hd : 0 < d) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < W a - W (a - ε) := by
  have hleft : Tendsto
      (fun t : ℝ => t⁻¹ * (W (a + t) - W a))
      (𝓝[<] (0 : ℝ)) (𝓝 d) := by
    simpa only [smul_eq_mul] using hD.tendsto_slope_zero_left
  have hneg : Tendsto (fun ε : ℝ => -ε)
      (𝓝[>] (0 : ℝ)) (𝓝[<] (0 : ℝ)) := by
    simpa only [neg_zero] using (tendsto_neg_nhdsGT (a := (0 : ℝ)))
  have hc := hleft.comp hneg
  change Tendsto (fun ε : ℝ =>
      (-ε)⁻¹ * (W (a + -ε) - W a)) (𝓝[>] (0 : ℝ)) (𝓝 d) at hc
  have hf : (fun ε : ℝ => (-ε)⁻¹ * (W (a + -ε) - W a)) =
      (fun ε : ℝ => ε⁻¹ * (W a - W (a - ε))) := by
    funext ε
    simp only [sub_eq_add_neg, inv_neg]
    ring
  rw [hf] at hc
  have hquot := Filter.Tendsto.eventually_const_lt hd hc
  filter_upwards [hquot, self_mem_nhdsWithin] with ε hq hε
  exact pos_of_mul_pos_right hq (le_of_lt (inv_pos.mpr hε))
