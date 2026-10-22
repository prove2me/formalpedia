-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_normalized_field_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:16:43.80115+00:00
-- url     : https://prove2.me/submissions/8d6db43a-dacd-4f85-a0ee-a2a85bf05fe0

import Theorems.Thm_BirkhoffGlobalSection_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y : Phase) (hy : y ∈ frontier M.body),
    ContDiffAt ℝ ∞ (fun z =>
      (phaseRadialContact z (hamiltonianVectorField M.modelHamiltonian z))⁻¹ •
        hamiltonianVectorField M.modelHamiltonian z) y := by
  exact BirkhoffGlobalSection.radial_variation_bundle.2.2.2.2.2.2.1
