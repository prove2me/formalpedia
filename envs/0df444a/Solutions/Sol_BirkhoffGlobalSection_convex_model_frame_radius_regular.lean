-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_frame_radius_regular
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:05:53.642987+00:00
-- url     : https://prove2.me/submissions/6b2e4861-cf55-40e7-86fc-56ec0125d28f

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (u : Phase) (hu : u ∈ unitThreeSphere),
    ContDiffAt ℝ ∞ (convexModelFrameRadius M) u ∧ 0 < convexModelFrameRadius M u := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.2.2.2.2.1
