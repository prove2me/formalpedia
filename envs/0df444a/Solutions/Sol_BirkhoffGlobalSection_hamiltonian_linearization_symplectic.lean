-- Prove2me | solution 1 for BirkhoffGlobalSection.hamiltonian_linearization_symplectic
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:49.153237+00:00
-- url     : https://prove2.me/submissions/34c0e9b3-697a-468c-a272-33053b620cf6

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (F : Phase → ℝ) (y v w : Phase)
    (hF : ContDiffAt ℝ ∞ F y),
    phaseSymplecticForm (fderiv ℝ (hamiltonianVectorField F) y v) w +
      phaseSymplecticForm v (fderiv ℝ (hamiltonianVectorField F) y w) = 0 := by
  exact BirkhoffGlobalSection.variational_symplecticity_bundle.2.2.2.1
