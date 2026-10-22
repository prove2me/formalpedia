-- Prove2me | solution 1 for BirkhoffGlobalSection.local_inward_negative_of_radial_derivative_pos
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:13:17.68098+00:00
-- url     : https://prove2.me/submissions/e5de82cd-e941-408e-b57a-78954ce3dcd2

import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

universe u_local_inward_negative_of_radial_derivative_pos

theorem solution :
∀ {E : Type u_local_inward_negative_of_radial_derivative_pos}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ) (s : E)
    (hc : DifferentiableAt ℝ F s) (hzero : F s = 0)
    (hrad : 0 < fderiv ℝ F s s),
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 1 - ε ≤ t → t < 1 → F (t • s) < 0 := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{0, u_local_inward_negative_of_radial_derivative_pos, 0}.2.2.2.2.2.2.2.2.2.1
