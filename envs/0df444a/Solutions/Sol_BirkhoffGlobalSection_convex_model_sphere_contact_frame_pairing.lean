-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_sphere_contact_frame_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:19:22.622086+00:00
-- url     : https://prove2.me/submissions/03e6bff6-fca8-4210-b4de-cb484f6894ab

import Theorems.Thm_BirkhoffGlobalSection_transverse_contact_frame_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
    let A := convexModelSphereContactFrame M u 0
    let B := convexModelSphereContactFrame M u 1
    let y := (gauge M.body u)⁻¹ • u
    fderiv ℝ (fun x => f x * phaseRadialContact x B) u A -
      fderiv ℝ (fun x => f x * phaseRadialContact x A) u B =
        zNormSq (TangentialHessian.grad M.modelHamiltonian y) +
          wNormSq (TangentialHessian.grad M.modelHamiltonian y) := by
  exact BirkhoffGlobalSection.transverse_contact_frame_bundle.2.2.2.2.2.2.2.2.1
