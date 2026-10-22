-- Prove2me | solution 1 for BirkhoffGlobalSection.hamiltonian_linearization_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:48.474951+00:00
-- url     : https://prove2.me/submissions/f3f6e4d5-52a6-4fc6-9031-472f1fc74a48

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (F : Phase → ℝ) (y v w : Phase)
    (hF : ContDiffAt ℝ ∞ F y),
    phaseSymplecticForm (fderiv ℝ (hamiltonianVectorField F) y v) w =
      fderiv ℝ (fderiv ℝ F) y v w := by
  exact BirkhoffGlobalSection.variational_symplecticity_bundle.2.2.1
