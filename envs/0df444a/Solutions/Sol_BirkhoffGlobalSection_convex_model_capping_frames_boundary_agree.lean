-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_capping_frames_boundary_agree
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:39.581281+00:00
-- url     : https://prove2.me/submissions/28daf39a-1c54-450e-89ee-a4130a8467c3

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (d₁ d₂ : ClosedDiskPoint → Phase)
    (hbd : ∀ z : {z : ClosedDiskPoint // z ∈ closedDiskBoundary}, d₁ z.val = d₂ z.val),
    ∀ z : {z : ClosedDiskPoint // z ∈ closedDiskBoundary}, ∀ i : Fin 2,
      convexModelSymplecticContactFrame M (d₁ z.val) i =
        convexModelSymplecticContactFrame M (d₂ z.val) i := by
  exact BirkhoffGlobalSection.contact_frame_angle_disk_bundle.{0}.2.2.2.2.2.2.2.2.2.2
