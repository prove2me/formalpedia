-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_positive_of_inward_negative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:12:41.932683+00:00
-- url     : https://prove2.me/submissions/372c2fe4-a831-4d9c-b3b8-e85c9c634feb

import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (hneg : ∀ y ∈ frontier M.body, ∀ t : ℝ, 0 ≤ t → t < 1 →
      M.modelHamiltonian (t • y) < 0),
    ∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y) := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{0, 0, 0}.2.2.2.2.2.1
