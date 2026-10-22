-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_coordinates_linear
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:05:58.245348+00:00
-- url     : https://prove2.me/submissions/dd644127-9aea-4ac2-a0d1-1bb38c7b325d

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v w : Phase) (a b : ℝ),
    convexModelContactCoordinates M u (a • v + b • w) =
      a • convexModelContactCoordinates M u v + b • convexModelContactCoordinates M u w := by
  exact BirkhoffGlobalSection.contact_frame_angle_disk_bundle.{0}.1
