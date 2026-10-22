-- Prove2me | solution 1 for BirkhoffGlobalSection.characteristic_contact_projection_linear
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:38:20.74638+00:00
-- url     : https://prove2.me/submissions/09946c1c-bc88-437f-88bd-e4e6a5c3e712

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (F : Phase → ℝ) (y v w : Phase) (a b : ℝ),
    characteristicContactProjection F y (a • v + b • w) =
      a • characteristicContactProjection F y v + b • characteristicContactProjection F y w := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.1
