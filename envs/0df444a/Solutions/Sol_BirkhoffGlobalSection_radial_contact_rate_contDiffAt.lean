-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_contact_rate_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:15:55.215993+00:00
-- url     : https://prove2.me/submissions/a8da8cc8-9371-4a8d-99b1-5bf222ec38ee

import Theorems.Thm_BirkhoffGlobalSection_model_contact_rate_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (X : Phase → Phase) (y : Phase)
    (hX : ContDiffAt ℝ ∞ X y),
    ContDiffAt ℝ ∞ (fun x => phaseRadialContact x (X x)) y := by
  exact BirkhoffGlobalSection.model_contact_rate_bundle.2.1
