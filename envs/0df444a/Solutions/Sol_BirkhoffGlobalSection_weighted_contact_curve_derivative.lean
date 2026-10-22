-- Prove2me | solution 1 for BirkhoffGlobalSection.weighted_contact_curve_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:06:40.968527+00:00
-- url     : https://prove2.me/submissions/0d36913d-7f2c-4349-8906-28e1edacc9ae

import Theorems.Thm_BirkhoffGlobalSection_contact_variation_preservation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (f : Phase → ℝ) (q v : ℝ → Phase)
    (t : ℝ) (a b : Phase) (hf : DifferentiableAt ℝ f (q t))
    (hq : HasDerivAt q a t) (hv : HasDerivAt v b t),
    HasDerivAt (fun s => f (q s) * phaseRadialContact (q s) (v s))
      (fderiv ℝ f (q t) a * phaseRadialContact (q t) (v t) +
        f (q t) * (phaseRadialContact a (v t) + phaseRadialContact (q t) b)) t := by
  exact BirkhoffGlobalSection.contact_variation_preservation_bundle.2.1
