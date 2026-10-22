-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_derivative_pos_of_local_inward_negative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:12:43.281984+00:00
-- url     : https://prove2.me/submissions/5a5474b6-43d5-43ee-94f6-fffd0b2f854b

import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

universe u_radial_derivative_pos_of_local_inward_negative

theorem solution :
∀ {E : Type u_radial_derivative_pos_of_local_inward_negative}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ) (s : E)
    (hsne : s ≠ 0) (hc : ContDiffAt ℝ 2 F s) (hzero : F s = 0)
    (hneg : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 1 - ε ≤ t → t < 1 → F (t • s) < 0)
    (hcurv : ∀ v : E, v ≠ 0 → fderiv ℝ F s v = 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v),
    0 < fderiv ℝ F s s := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{u_radial_derivative_pos_of_local_inward_negative, 0, 0}.2.2.2.2.2.2.2.1
