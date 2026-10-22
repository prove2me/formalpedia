-- Prove2me | solution 1 for BirkhoffGlobalSection.scaled_hamiltonian_linearization_symplectic
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:49.767089+00:00
-- url     : https://prove2.me/submissions/76000596-603a-4c78-89cf-c49092a01c2c

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (F b : Phase → ℝ) (y v w : Phase)
    (hF : ContDiffAt ℝ ∞ F y) (hb : DifferentiableAt ℝ b y)
    (hv : fderiv ℝ F y v = 0) (hw : fderiv ℝ F y w = 0),
    phaseSymplecticForm (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) y v) w +
      phaseSymplecticForm v (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) y w) = 0 := by
  exact BirkhoffGlobalSection.variational_symplecticity_bundle.2.2.2.2.1
