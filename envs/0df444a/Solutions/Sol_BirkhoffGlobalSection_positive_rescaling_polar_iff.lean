-- Prove2me | solution 1 for BirkhoffGlobalSection.positive_rescaling_polar_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:02.386631+00:00
-- url     : https://prove2.me/submissions/7ea73057-5e63-4c37-ba6b-53cf8739d6d4

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (p q : Plane) (a θ : ℝ)
    (ha : 0 < a) (hq : q = a • p),
    (∃ r : ℝ, 0 < r ∧ p = ![r * Real.cos θ, r * Real.sin θ]) ↔
    (∃ r : ℝ, 0 < r ∧ q = ![r * Real.cos θ, r * Real.sin θ]) := by
  exact BirkhoffGlobalSection.contact_frame_angle_disk_bundle.{0}.2.2.2.2.2.1
