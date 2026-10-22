-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_symplectic_contact_frame_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:05:55.576986+00:00
-- url     : https://prove2.me/submissions/426f90c8-5221-4f50-b3df-767df670b3ef

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    let f : Phase → ℝ := fun x => ((gauge M.body x)⁻¹)^2
    let A := convexModelSymplecticContactFrame M u 0
    let B := convexModelSymplecticContactFrame M u 1
    fderiv ℝ (fun x => f x * phaseRadialContact x B) u A -
      fderiv ℝ (fun x => f x * phaseRadialContact x A) u B = 1 := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.2.2.2.2.2.2.2.1
