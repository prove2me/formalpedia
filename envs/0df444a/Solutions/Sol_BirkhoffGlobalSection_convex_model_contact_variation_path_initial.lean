-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_variation_path_initial
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:45.485615+00:00
-- url     : https://prove2.me/submissions/1b39c735-760d-4a28-b042-b2197f801a80

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : q 0 ∈ unitThreeSphere)
    (hZ0 : Z 0 = ContinuousLinearMap.id ℝ Phase) (p : Plane),
    convexModelContactVariationPath M q Z 0 p = p := by
  exact BirkhoffGlobalSection.contact_variation_preservation_bundle.2.2.2.2.2.2.2.2.1
