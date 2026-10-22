-- Prove2me | solution 1 for BirkhoffGlobalSection.first_integral_variation_conserved
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:17:33.997987+00:00
-- url     : https://prove2.me/submissions/0b05809d-ce64-4c7b-8939-f087231dd161

import Theorems.Thm_BirkhoffGlobalSection_reverse_radial_variation_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (F : Phase → ℝ) (X : Phase → Phase)
    (x v : ℝ → Phase) (hF : ∀ t, ContDiffAt ℝ ∞ F (x t))
    (hX : ∀ t, DifferentiableAt ℝ X (x t))
    (hx : ∀ t, HasDerivAt x (X (x t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ X (x t) (v t)) t)
    (hzero : ∀ t, (fun y => fderiv ℝ F y (X y)) =ᶠ[𝓝 (x t)] (fun _ => (0 : ℝ))),
    ∀ t, fderiv ℝ F (x t) (v t) = fderiv ℝ F (x 0) (v 0) := by
  exact BirkhoffGlobalSection.reverse_radial_variation_bundle.2.1
