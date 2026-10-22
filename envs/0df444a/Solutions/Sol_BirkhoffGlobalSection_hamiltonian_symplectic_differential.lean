-- Prove2me | solution 1 for BirkhoffGlobalSection.hamiltonian_symplectic_differential
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:47.885241+00:00
-- url     : https://prove2.me/submissions/aecc21bb-c09a-4d8a-980e-93b9e61298df

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (F : Phase → ℝ) (y v : Phase),
    phaseSymplecticForm (hamiltonianVectorField F y) v = fderiv ℝ F y v := by
  exact BirkhoffGlobalSection.variational_symplecticity_bundle.2.1
