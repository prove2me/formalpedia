-- Prove2me | solution 1 for BlackScholesModel.dPlus_spot_tail_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T15:43:35.396967+00:00
-- url     : https://prove2.me/submissions/8cb62fac-fd31-41ae-aca4-ab99d76c2e71

import Mathlib
import Definitions.Def_BlackScholesModel_Core

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- The logarithmic Black-Scholes argument has the expected spot tails. -/
theorem solution (K r σ τ : ℝ) (hK : 0 < K)
    (hσ : 0 < σ) (hτ : 0 < τ) :
    Tendsto (fun S => dPlus S K r σ τ) (𝓝[>] 0) atBot ∧
    Tendsto (fun S => dPlus S K r σ τ) atTop atTop := by
  have hden : 0 < σ * Real.sqrt τ :=
    mul_pos hσ (Real.sqrt_pos.2 hτ)
  have hlogbot :
      Tendsto (fun S : ℝ => Real.log (S / K)) (𝓝[>] 0) atBot := by
    have hh : Tendsto
        (fun S : ℝ => Real.log S - Real.log K) (𝓝[>] 0) atBot := by
      simpa only [sub_eq_add_neg] using
        (Filter.tendsto_atBot_add_const_right
          (𝓝[>] (0 : ℝ)) (-Real.log K)
          Real.tendsto_log_nhdsGT_zero)
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with S hS
    exact (Real.log_div (ne_of_gt hS) (ne_of_gt hK)).symm
  have hlogtop :
      Tendsto (fun S : ℝ => Real.log (S / K)) atTop atTop := by
    have hh : Tendsto
        (fun S : ℝ => Real.log S - Real.log K) atTop atTop := by
      simpa only [sub_eq_add_neg] using
        (Filter.tendsto_atTop_add_const_right atTop (-Real.log K)
          Real.tendsto_log_atTop)
    apply hh.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with S hS
    exact (Real.log_div (ne_of_gt hS) (ne_of_gt hK)).symm
  have hnumBot : Tendsto
      (fun S : ℝ => Real.log (S / K) + (r + σ ^ 2 / 2) * τ)
      (𝓝[>] 0) atBot :=
    Filter.tendsto_atBot_add_const_right (𝓝[>] (0 : ℝ))
      ((r + σ ^ 2 / 2) * τ) hlogbot
  have hnumTop : Tendsto
      (fun S : ℝ => Real.log (S / K) + (r + σ ^ 2 / 2) * τ)
      atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop
      ((r + σ ^ 2 / 2) * τ) hlogtop
  constructor
  · change Tendsto (fun S : ℝ =>
        (Real.log (S / K) + (r + σ ^ 2 / 2) * τ) /
          (σ * Real.sqrt τ)) (𝓝[>] 0) atBot
    exact (Filter.tendsto_div_const_atBot_of_pos hden).2 hnumBot
  · change Tendsto (fun S : ℝ =>
        (Real.log (S / K) + (r + σ ^ 2 / 2) * τ) /
          (σ * Real.sqrt τ)) atTop atTop
    exact (Filter.tendsto_div_const_atTop_of_pos hden).2 hnumTop
