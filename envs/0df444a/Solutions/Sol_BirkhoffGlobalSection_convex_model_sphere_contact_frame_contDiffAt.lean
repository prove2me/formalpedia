-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_sphere_contact_frame_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:05:52.996987+00:00
-- url     : https://prove2.me/submissions/7857f5b0-a54d-42a5-ac7a-64754c4bdf74

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere) (i : Fin 2),
    ContDiffAt ℝ ∞ (fun z => convexModelSphereContactFrame M z i) u := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.2.2.2.1
