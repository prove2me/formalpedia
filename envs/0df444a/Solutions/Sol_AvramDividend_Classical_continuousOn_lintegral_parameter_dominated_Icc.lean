-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_lintegral_parameter_dominated_Icc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:38:48.745984+00:00
-- url     : https://prove2.me/submissions/aa8bc42c-ff48-4ed1-8c9c-326217cd3c3c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set

/-- The exact dominated-continuity bridge for Laplace-parameter-dependent integrals. -/
theorem solution
    (ν : Measure ℝ) (a b : ℝ) (F : ℝ → ℝ → ℝ) (bound : ℝ → ℝ)
    (hmeas : ∀ θ ∈ Icc a b, AEStronglyMeasurable (F θ) ν)
    (hbound : ∀ θ ∈ Icc a b, ∀ᵐ y : ℝ ∂ν, ‖F θ y‖ ≤ bound y)
    (hboundInt : Integrable bound ν)
    (hcont : ∀ᵐ y : ℝ ∂ν, Continuous (fun z : Icc a b => F z.1 y)) :
    ContinuousOn (fun θ : ℝ => ∫ y : ℝ, F θ y ∂ν) (Icc a b) := by
  apply continuousOn_iff_continuous_restrict.mpr
  exact MeasureTheory.continuous_of_dominated
    (F := fun z : Icc a b => fun y : ℝ => F z.1 y)
    (bound := bound)
    (fun z => hmeas z.1 z.2)
    (fun z => hbound z.1 z.2)
    hboundInt hcont
