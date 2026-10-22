-- Prove2me | solution 1 for BirkhoffGlobalSection.hamiltonian_radial_contact_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:12:41.358689+00:00
-- url     : https://prove2.me/submissions/582a7191-e60d-464a-8748-f77e197eda58

import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (F : Phase → ℝ) (y : Phase),
    phaseRadialContact y (hamiltonianVectorField F y) = fderiv ℝ F y y / 2 := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{0, 0, 0}.2.2.2.2.1
