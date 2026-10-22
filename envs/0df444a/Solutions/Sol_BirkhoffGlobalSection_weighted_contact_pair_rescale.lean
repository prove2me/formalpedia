-- Prove2me | solution 1 for BirkhoffGlobalSection.weighted_contact_pair_rescale
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:05:54.899632+00:00
-- url     : https://prove2.me/submissions/bca8e647-9f1d-477e-baf2-3f3a7e61cf6b

import Theorems.Thm_BirkhoffGlobalSection_contact_frame_basis_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (f : Phase → ℝ) (u v w : Phase) (a b : ℝ)
    (hf : DifferentiableAt ℝ f u),
    fderiv ℝ (fun x => f x * phaseRadialContact x (b • w)) u (a • v) -
      fderiv ℝ (fun x => f x * phaseRadialContact x (a • v)) u (b • w) =
      a * b * (fderiv ℝ (fun x => f x * phaseRadialContact x w) u v -
        fderiv ℝ (fun x => f x * phaseRadialContact x v) u w) := by
  exact BirkhoffGlobalSection.contact_frame_basis_bundle.2.2.2.2.2.2.2.2.2.2.2.1
