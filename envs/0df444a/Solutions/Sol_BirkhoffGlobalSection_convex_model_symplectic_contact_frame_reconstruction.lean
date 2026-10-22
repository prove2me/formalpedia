-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_symplectic_contact_frame_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:05:56.851451+00:00
-- url     : https://prove2.me/submissions/8a4deff4-3079-418c-9b41-459244cfa55e

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
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
    let G : Phase → Phase := fun x => (gauge M.body x)⁻¹ • x
    let c := transverseFrameCoordinates (TangentialHessian.grad M.modelHamiltonian (G u)) (fderiv ℝ G u v)
    v = (c 0 / Real.sqrt (convexModelFrameRadius M u)) • convexModelSymplecticContactFrame M u 0 +
      (c 1 / Real.sqrt (convexModelFrameRadius M u)) • convexModelSymplecticContactFrame M u 1 := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
