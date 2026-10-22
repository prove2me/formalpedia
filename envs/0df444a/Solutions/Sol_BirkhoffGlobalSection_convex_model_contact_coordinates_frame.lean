-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_coordinates_frame
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:05:58.934324+00:00
-- url     : https://prove2.me/submissions/45dca5bc-6dfd-43ba-a18f-9d64b7ead553

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    convexModelContactCoordinates M u (convexModelSymplecticContactFrame M u 0) = ![1, 0] ∧
    convexModelContactCoordinates M u (convexModelSymplecticContactFrame M u 1) = ![0, 1] := by
  exact BirkhoffGlobalSection.contact_frame_angle_disk_bundle.{0}.2.1
