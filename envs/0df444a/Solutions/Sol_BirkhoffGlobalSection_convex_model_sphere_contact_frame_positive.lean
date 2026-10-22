-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_sphere_contact_frame_positive
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:36:59.890448+00:00
-- url     : https://prove2.me/submissions/74678cb6-60b0-4ea4-9d45-990b8d6631df

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
    0 < fderiv ℝ (fun x => f x * phaseRadialContact x B) u A -
      fderiv ℝ (fun x => f x * phaseRadialContact x A) u B := by
  exact BirkhoffGlobalSection.transverse_contact_frame_bundle.2.2.2.2.2.2.2.2.2.2.2
