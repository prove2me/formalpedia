-- Prove2me | solution 1 for BirkhoffGlobalSection.hamiltonian_quaternionic_transverse_tangent
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:18:28.088001+00:00
-- url     : https://prove2.me/submissions/d03a3dd7-8401-4af5-8a90-7b27a071c8f5

import Theorems.Thm_BirkhoffGlobalSection_transverse_contact_frame_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (F : Phase → ℝ) (y : Phase),
    fderiv ℝ F y (TangentialHessian.frame (TangentialHessian.grad F y) 1) = 0 ∧
    fderiv ℝ F y (TangentialHessian.frame (TangentialHessian.grad F y) 2) = 0 := by
  exact BirkhoffGlobalSection.transverse_contact_frame_bundle.2.1
