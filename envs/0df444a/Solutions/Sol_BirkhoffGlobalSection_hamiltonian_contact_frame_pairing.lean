-- Prove2me | solution 1 for BirkhoffGlobalSection.hamiltonian_contact_frame_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:18:29.440167+00:00
-- url     : https://prove2.me/submissions/ab98f793-ead9-4a67-85f9-49724bb8ab1f

import Theorems.Thm_BirkhoffGlobalSection_transverse_contact_frame_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (F : Phase → ℝ) (y : Phase)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y)),
    phaseSymplecticForm (hamiltonianContactFrame F y 0) (hamiltonianContactFrame F y 1) =
      -(zNormSq (TangentialHessian.grad F y) + wNormSq (TangentialHessian.grad F y)) := by
  exact BirkhoffGlobalSection.transverse_contact_frame_bundle.2.2.2.1
