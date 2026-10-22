-- Prove2me | solution 1 for BirkhoffGlobalSection.plane_curve_polar_bound_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:07:33.589994+00:00
-- url     : https://prove2.me/submissions/f24fc2fd-217e-4fba-8856-baca9eb9127f

import Theorems.Thm_BirkhoffGlobalSection_contact_angular_lift_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (v : ℝ → Plane) (hv : Continuous v)
    (hne : ∀ t, v t ≠ 0) (T L : ℝ),
    (∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ v t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      L < θ T - θ 0) ↔
    ∃ ρ θ : ℝ → ℝ, Continuous ρ ∧ Continuous θ ∧ (∀ t, 0 < ρ t) ∧
      (∀ t, v t = ![ρ t * Real.cos (θ t), ρ t * Real.sin (θ t)]) ∧ L < θ T - θ 0 := by
  exact BirkhoffGlobalSection.contact_angular_lift_bundle.2.2.2.2.2.2.2
