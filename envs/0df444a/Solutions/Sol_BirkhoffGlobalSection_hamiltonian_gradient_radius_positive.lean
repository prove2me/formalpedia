-- Prove2me | solution 1 for BirkhoffGlobalSection.hamiltonian_gradient_radius_positive
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:18:30.799981+00:00
-- url     : https://prove2.me/submissions/58eec839-abe0-48df-a19c-caa9cc263288

import Theorems.Thm_BirkhoffGlobalSection_transverse_contact_frame_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (F : Phase → ℝ) (y : Phase)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y)),
    0 < zNormSq (TangentialHessian.grad F y) + wNormSq (TangentialHessian.grad F y) := by
  exact BirkhoffGlobalSection.transverse_contact_frame_bundle.2.2.2.2.2.2.1
