-- Prove2me | solution 1 for BirkhoffGlobalSection.characteristic_contact_projection_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:39:46.999772+00:00
-- url     : https://prove2.me/submissions/77deeda3-7482-4b44-9d45-fe7420af5300

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (F : Phase → ℝ) (V : Phase → Phase)
    (y : Phase) (hF : ContDiffAt ℝ ∞ F y) (hV : ContDiffAt ℝ ∞ V y)
    (hp : 0 < phaseRadialContact y (hamiltonianVectorField F y)),
    ContDiffAt ℝ ∞ (fun z => characteristicContactProjection F z (V z)) y := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.2.1
