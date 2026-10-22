-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_symplectic_contact_frame_independent
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:05:57.549984+00:00
-- url     : https://prove2.me/submissions/0cccab7c-0fc3-4e7e-aeae-54433cb2e510

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere)
    (a b : ℝ) (hz : a • convexModelSymplecticContactFrame M u 0 +
      b • convexModelSymplecticContactFrame M u 1 = 0),
    a = 0 ∧ b = 0 := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
