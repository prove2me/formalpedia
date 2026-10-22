-- Prove2me | solution 1 for BirkhoffGlobalSection.quaternionic_vector_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:38:20.237416+00:00
-- url     : https://prove2.me/submissions/ce8a09f1-21d2-4775-afcb-3d1181b4206f

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (g v : Phase),
    (zNormSq g + wNormSq g) • v = (v ⬝ᵥ g) • g +
      (v ⬝ᵥ TangentialHessian.frame g 0) • TangentialHessian.frame g 0 +
      (v ⬝ᵥ TangentialHessian.frame g 1) • TangentialHessian.frame g 1 +
      (v ⬝ᵥ TangentialHessian.frame g 2) • TangentialHessian.frame g 2 := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.1
