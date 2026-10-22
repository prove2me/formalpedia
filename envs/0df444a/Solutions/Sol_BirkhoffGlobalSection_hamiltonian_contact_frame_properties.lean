-- Prove2me | solution 1 for BirkhoffGlobalSection.hamiltonian_contact_frame_properties
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:19:21.995547+00:00
-- url     : https://prove2.me/submissions/3565a134-a26e-414d-af60-fe576b92cc06

import Theorems.Thm_BirkhoffGlobalSection_transverse_contact_frame_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (F : Phase → ℝ) (y : Phase)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y)) (i : Fin 2),
    fderiv ℝ F y (hamiltonianContactFrame F y i) = 0 ∧
      phaseRadialContact y (hamiltonianContactFrame F y i) = 0 := by
  exact BirkhoffGlobalSection.transverse_contact_frame_bundle.2.2.2.2.1
