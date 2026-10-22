-- Prove2me | solution 1 for BirkhoffGlobalSection.hamiltonian_vector_field_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:15:54.268232+00:00
-- url     : https://prove2.me/submissions/15f28fef-5405-4f0f-811a-956a8f046520

import Theorems.Thm_BirkhoffGlobalSection_model_contact_rate_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (F : Phase → ℝ) (y : Phase)
    (hF : ContDiffAt ℝ ∞ F y),
    ContDiffAt ℝ ∞ (hamiltonianVectorField F) y := by
  exact BirkhoffGlobalSection.model_contact_rate_bundle.1
