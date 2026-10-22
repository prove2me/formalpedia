-- Prove2me | solution 1 for BirkhoffGlobalSection.local_inward_negative_derivative_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:12:42.568984+00:00
-- url     : https://prove2.me/submissions/52a5314b-aa8e-4440-8553-c7fbb8dd951b

import Theorems.Thm_BirkhoffGlobalSection_radial_characteristic_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (f : ℝ → ℝ) (d ε : ℝ)
    (hε : 0 < ε) (hd : HasDerivAt f d 1) (hzero : f 1 = 0)
    (hneg : ∀ t : ℝ, 1 - ε ≤ t → t < 1 → f t < 0),
    0 ≤ d := by
  exact BirkhoffGlobalSection.radial_characteristic_bundle.{0, 0, 0}.2.2.2.2.2.2.1
