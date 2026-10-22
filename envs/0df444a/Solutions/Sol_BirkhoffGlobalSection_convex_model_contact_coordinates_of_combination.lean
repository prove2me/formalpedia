-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_coordinates_of_combination
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:00.797038+00:00
-- url     : https://prove2.me/submissions/0eab6126-c6fe-439f-9eef-73124708978d

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere) (a b : ℝ),
    convexModelContactCoordinates M u (a • convexModelSymplecticContactFrame M u 0 +
      b • convexModelSymplecticContactFrame M u 1) = ![a, b] := by
  exact BirkhoffGlobalSection.contact_frame_angle_disk_bundle.{0}.2.2.2.1
