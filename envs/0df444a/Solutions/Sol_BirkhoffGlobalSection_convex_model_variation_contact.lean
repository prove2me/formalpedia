-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_variation_contact
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:43.594645+00:00
-- url     : https://prove2.me/submissions/2def182d-2b08-4e33-b495-e2e65f68330c

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (q v : ℝ → Phase)
    (hqS : ∀ t, q t ∈ unitThreeSphere)
    (hq : ∀ t, HasDerivAt q (convexModelSphereReebField M (q t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ (convexModelSphereReebField M) (q t) (v t)) t)
    (h0 : q 0 0 * v 0 0 + q 0 1 * v 0 1 + q 0 2 * v 0 2 + q 0 3 * v 0 3 = 0)
    (hα0 : phaseRadialContact (q 0) (v 0) = 0),
    ∀ t, (q t 0 * v t 0 + q t 1 * v t 1 + q t 2 * v t 2 + q t 3 * v t 3 = 0) ∧
      phaseRadialContact (q t) (v t) = 0 := by
  exact BirkhoffGlobalSection.contact_variation_preservation_bundle.2.2.2.2.2.1
