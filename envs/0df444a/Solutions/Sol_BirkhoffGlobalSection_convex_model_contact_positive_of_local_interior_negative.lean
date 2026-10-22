-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_positive_of_local_interior_negative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:13:20.015924+00:00
-- url     : https://prove2.me/submissions/d25ac693-cac4-43aa-8ab5-7d66c23ad245

import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c)
    (hneg : ∀ y ∈ frontier M.body, ∀ᶠ x in nhds y,
      x ∈ interior M.body → M.modelHamiltonian x < 0),
    ∀ y ∈ frontier M.body,
      0 < phaseRadialContact y (hamiltonianVectorField M.modelHamiltonian y) := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{0, 0, 0}.2.2.2.2.2.2.2.2.2.2.2.2
