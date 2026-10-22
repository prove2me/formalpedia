-- Prove2me | solution 1 for BirkhoffGlobalSection.positive_rescaling_angular_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:03.088746+00:00
-- url     : https://prove2.me/submissions/4e2ad17b-8d8d-4f2a-bba0-66d5d7ff03e7

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (p q : ℝ → Plane) (a : ℝ → ℝ) (T B : ℝ)
    (ha : ∀ t, 0 < a t) (heq : ∀ t, q t = a t • p t)
    (hbound : ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ p t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      B < θ T - θ 0),
    ∀ θ : ℝ → ℝ, Continuous θ →
      (∀ t, ∃ r : ℝ, 0 < r ∧ q t = ![r * Real.cos (θ t), r * Real.sin (θ t)]) →
      B < θ T - θ 0 := by
  exact BirkhoffGlobalSection.contact_frame_angle_disk_bundle.{0}.2.2.2.2.2.2.1
