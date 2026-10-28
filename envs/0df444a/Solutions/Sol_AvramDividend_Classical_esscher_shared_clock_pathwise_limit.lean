-- Prove2me | solution 1 for AvramDividend.Classical.esscher_shared_clock_pathwise_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T13:40:17.614693+00:00
-- url     : https://prove2.me/submissions/76ce0d55-1ce5-40e1-ad9c-c794e5620dd1

import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set

/-- A shared positive clock seed E couples clocks E/p and transfers path limits. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) (E : Ω → ℝ)
    (Y : ℝ → Ω → ℝ) (Yinf : Ω → ℝ)
    (hE : ∀ᵐ ω ∂Q, 0 < E ω)
    (hY : ∀ᵐ ω ∂Q,
      Tendsto (fun t : ℝ => Y t ω) atTop (nhds (Yinf ω))) :
    ∀ᵐ ω ∂Q, Tendsto (fun p : ℝ => Y (E ω / p) ω)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (Yinf ω)) := by
  filter_upwards [hE, hY] with ω hω hlim
  have hclock : Tendsto (fun p : ℝ => E ω / p)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
    simpa only [div_eq_mul_inv] using
      (Filter.Tendsto.const_mul_atTop hω
        (tendsto_inv_nhdsGT_zero :
          Tendsto (fun p : ℝ => p⁻¹)
            (nhdsWithin (0 : ℝ) (Ioi 0)) atTop))
  exact hlim.comp hclock
