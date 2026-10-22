-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_coordinates_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:05:59.938011+00:00
-- url     : https://prove2.me/submissions/8f4856f4-0711-40a0-b74b-899f8f7bfda8

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_angle_disk_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u v : Phase) (hu : u ∈ unitThreeSphere)
    (hv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0)
    (hα : phaseRadialContact u v = 0),
    v = (convexModelContactCoordinates M u v 0) • convexModelSymplecticContactFrame M u 0 +
      (convexModelContactCoordinates M u v 1) • convexModelSymplecticContactFrame M u 1 := by
  exact BirkhoffGlobalSection.contact_frame_angle_disk_bundle.{0}.2.2.1
