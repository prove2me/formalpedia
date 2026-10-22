-- Prove2me | solution 1 for BirkhoffGlobalSection.differential_dot_gradient
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:37:39.013881+00:00
-- url     : https://prove2.me/submissions/3c8125e2-604e-4a11-b550-37169f084989

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (F : Phase → ℝ) (y v : Phase),
    fderiv ℝ F y v = v ⬝ᵥ TangentialHessian.grad F y := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.1
