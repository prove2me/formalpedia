-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_coordinates_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:44.269644+00:00
-- url     : https://prove2.me/submissions/df0ce45c-0300-441a-85e6-bc06fb408fd8

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q v : ℝ → Phase)
    (hq : Continuous q) (hv : Continuous v) (hs : ∀ t, q t ∈ unitThreeSphere),
    Continuous (fun t => convexModelContactCoordinates M (q t) (v t)) := by
  exact BirkhoffGlobalSection.contact_variation_preservation_bundle.2.2.2.2.2.2.1
