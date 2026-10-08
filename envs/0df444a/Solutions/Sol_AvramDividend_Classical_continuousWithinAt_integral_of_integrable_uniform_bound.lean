-- Prove2me | solution 1 for AvramDividend.Classical.continuousWithinAt_integral_of_integrable_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:09:57.789114+00:00
-- url     : https://prove2.me/submissions/46b6993b-79ee-427f-a3f2-310d82a12175

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem solution
    (μ : Measure ℝ) (s : Set ℝ) (F : ℝ → ℝ → ℝ)
    (bound : ℝ → ℝ) (x0 : ℝ) (hx0 : x0 ∈ s)
    (hmeas : ∀ x ∈ s, AEStronglyMeasurable (F x) μ)
    (hbound : ∀ x ∈ s, ∀ᵐ y ∂μ, ‖F x y‖ ≤ bound y)
    (hbound_int : Integrable bound μ)
    (hcont : ∀ᵐ y ∂μ, ContinuousWithinAt (fun x => F x y) s x0) :
    ContinuousWithinAt (fun x => ∫ y, F x y ∂μ) s x0 := by
  apply tendsto_integral_filter_of_dominated_convergence bound
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact hmeas x hx
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact hbound x hx
  · exact hbound_int
  · exact hcont
