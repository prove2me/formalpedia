-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_variation_path_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:46.100135+00:00
-- url     : https://prove2.me/submissions/77716139-1fcc-4299-a818-f0df90312526

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q : ℝ → Phase)
    (Z : ℝ → (Phase →L[ℝ] Phase)) (hs : ∀ t, q t ∈ unitThreeSphere)
    (hq : Continuous q) (hZ : Continuous Z) (p : Plane),
    Continuous (fun t => convexModelContactVariationPath M q Z t p) := by
  exact BirkhoffGlobalSection.contact_variation_preservation_bundle.2.2.2.2.2.2.2.2.2.1
