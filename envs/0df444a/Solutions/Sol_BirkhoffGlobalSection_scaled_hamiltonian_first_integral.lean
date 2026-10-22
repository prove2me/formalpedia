-- Prove2me | solution 1 for BirkhoffGlobalSection.scaled_hamiltonian_first_integral
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:17:33.130455+00:00
-- url     : https://prove2.me/submissions/39a0e881-4428-4fba-9f44-157716a28c45

import Theorems.Thm_BirkhoffGlobalSection_reverse_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (F b : Phase → ℝ) (y : Phase),
    fderiv ℝ F y (b y • hamiltonianVectorField F y) = 0 := by
  exact BirkhoffGlobalSection.reverse_radial_variation_bundle.1
