-- Prove2me | solution 1 for BirkhoffGlobalSection.hamiltonian_contact_frame_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:39:01.83603+00:00
-- url     : https://prove2.me/submissions/09fed6a9-ae0e-46e3-80a2-4d5f538b887c

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (F : Phase → ℝ) (y v : Phase)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y))
    (hv : fderiv ℝ F y v = 0) (hα : phaseRadialContact y v = 0),
    let g := TangentialHessian.grad F y
    let n := zNormSq g + wNormSq g
    let c := transverseFrameCoordinates g v
    v = (c 0 / n) • hamiltonianContactFrame F y 0 +
      (c 1 / n) • hamiltonianContactFrame F y 1 := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.1
