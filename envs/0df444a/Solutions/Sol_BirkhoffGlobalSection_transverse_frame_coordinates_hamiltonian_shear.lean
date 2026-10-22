-- Prove2me | solution 1 for BirkhoffGlobalSection.transverse_frame_coordinates_hamiltonian_shear
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:13:23.563975+00:00
-- url     : https://prove2.me/submissions/36d0a847-0222-44c0-992d-7e8e23abc86c

import Theorems.Thm_BirkhoffGlobalSection_positive_time_change_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (F : Phase → ℝ) (y w : Phase) (c : ℝ),
    transverseFrameCoordinates (TangentialHessian.grad F y)
      (w + c • hamiltonianVectorField F y) =
        transverseFrameCoordinates (TangentialHessian.grad F y) w := by
  exact BirkhoffGlobalSection.positive_time_change_bundle.{0, 0}.1
