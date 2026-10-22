-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_sphere_contact_frame_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:39:02.98502+00:00
-- url     : https://prove2.me/submissions/790f2f01-8c76-4123-b7a5-dfe769422088

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
    let g := TangentialHessian.grad M.modelHamiltonian (G u)
    let n := zNormSq g + wNormSq g
    let c := transverseFrameCoordinates g (fderiv ℝ G u v)
    v = (c 0 / n) • convexModelSphereContactFrame M u 0 +
      (c 1 / n) • convexModelSphereContactFrame M u 1 := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.1
