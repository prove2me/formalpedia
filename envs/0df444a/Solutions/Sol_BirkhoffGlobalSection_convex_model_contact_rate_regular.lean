-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_contact_rate_regular
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:15:55.782078+00:00
-- url     : https://prove2.me/submissions/5758ffd7-04ce-4f1f-8228-898513d47de2

import Theorems.Thm_BirkhoffGlobalSection_model_contact_rate_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (y : Phase) (hy : y ∈ frontier M.body),
    let r : Phase → ℝ := fun x =>
      phaseRadialContact x (hamiltonianVectorField M.modelHamiltonian x)
    ContDiffAt ℝ ∞ (hamiltonianVectorField M.modelHamiltonian) y ∧
      ContDiffAt ℝ ∞ r y ∧ ContDiffAt ℝ ∞ (fun x => (r x)⁻¹) y ∧
      0 < (r y)⁻¹ := by
  exact BirkhoffGlobalSection.model_contact_rate_bundle.2.2.1
