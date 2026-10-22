-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_contact_curve_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:40.226375+00:00
-- url     : https://prove2.me/submissions/3a3ef120-9bc5-491b-a423-b9d4860fcef7

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (q v : ℝ → Phase) (t : ℝ) (a b : Phase)
    (hq : HasDerivAt q a t) (hv : HasDerivAt v b t),
    HasDerivAt (fun s => phaseRadialContact (q s) (v s))
      (phaseRadialContact a (v t) + phaseRadialContact (q t) b) t := by
  exact BirkhoffGlobalSection.contact_variation_preservation_bundle.1
