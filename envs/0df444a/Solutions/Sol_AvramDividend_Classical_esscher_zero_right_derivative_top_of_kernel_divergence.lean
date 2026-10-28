-- Prove2me | solution 1 for AvramDividend.Classical.esscher_zero_right_derivative_top_of_kernel_divergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:24:10.535677+00:00
-- url     : https://prove2.me/submissions/7be5575e-848d-46ef-b0a9-15ae3ba09d16

import Theorems.Thm_AvramDividend_Classical_esscher_scale_derivative_diverges_of_kernel_diverges
import Theorems.Thm_AvramDividend_Classical_derivZeroPlus_eq_top_of_right_tendsto_atTop
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped Topology

/-- The derivative growth transfers to the extended right boundary slope. -/
theorem solution
    (W : ℝ → ℝ) (φ c : ℝ) (f k : ℝ → ℝ)
    (hφ : 0 ≤ φ)
    (hW : ∀ x : ℝ, 0 < x → W x =
      Real.exp (φ * x) * (c + ∫ t in (0 : ℝ)..x, f t))
    (hint : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x)
    (hmeas : ∀ x : ℝ, 0 < x → StronglyMeasurableAtFilter f (𝓝 x) volume)
    (hcont : ∀ x : ℝ, 0 < x → ContinuousAt f x)
    (hFnonneg : ∀ x : ℝ, 0 < x → 0 ≤ c + ∫ t in (0 : ℝ)..x, f t)
    (hfnonneg : ∀ x : ℝ, 0 < x → 0 ≤ f x)
    (hk : ∀ x : ℝ, 0 < x → k x ≤ f x)
    (hkTop : Tendsto k (nhdsWithin (0 : ℝ) (Ioi 0)) atTop) :
    derivZeroPlus W = ⊤ := by
  apply derivZeroPlus_eq_top_of_right_tendsto_atTop W
  exact esscher_scale_derivative_diverges_of_kernel_diverges W φ c f k
    hφ hW hint hmeas hcont hFnonneg hfnonneg hk hkTop
