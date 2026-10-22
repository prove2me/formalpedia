-- Prove2me | solution 1 for BirkhoffGlobalSection.continuous_angle_increment_unique
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:07:30.054963+00:00
-- url     : https://prove2.me/submissions/587e6cf2-09a7-4597-90f7-60111d48aeb0

import Theorems.Thm_BirkhoffGlobalSection_contact_angular_lift_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (θ ψ : ℝ → ℝ)
    (hθ : Continuous θ) (hψ : Continuous ψ)
    (hcos : ∀ t, Real.cos (θ t) = Real.cos (ψ t))
    (hsin : ∀ t, Real.sin (θ t) = Real.sin (ψ t)),
    ∀ t, θ t - θ 0 = ψ t - ψ 0 := by
  exact BirkhoffGlobalSection.contact_angular_lift_bundle.2.2.1
