-- Prove2me | solution 1 for AvramDividend.Classical.esscher_scale_derivative_diverges_of_kernel_diverges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:13:22.499187+00:00
-- url     : https://prove2.me/submissions/06de9741-f2b9-4082-a9a3-affcf3e803c5

import Theorems.Thm_AvramDividend_Classical_esscher_scale_deriv_lower_of_renewal_identity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped Topology

/-- A locally dominating derivative inherits the kernel's positive-origin divergence. -/
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
    Tendsto (deriv W) (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  have hbound := esscher_scale_deriv_lower_of_renewal_identity W φ c f k
    hφ hW hint hmeas hcont hFnonneg hfnonneg hk
  rw [Filter.tendsto_atTop] at hkTop ⊢
  intro b
  filter_upwards [hkTop b, self_mem_nhdsWithin] with x hxb hxp
  have hx : 0 < x := hxp
  exact hxb.trans (hbound x hx)
