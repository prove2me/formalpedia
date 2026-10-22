-- Prove2me | solution 1 for BirkhoffGlobalSection.complex_curve_log_lift
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:07:28.54626+00:00
-- url     : https://prove2.me/submissions/efc529bd-0331-42bb-9837-38adfe147e4d

import Theorems.Thm_BirkhoffGlobalSection_contact_angular_lift_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (z : ℝ → ℂ) (hz : Continuous z)
    (hne : ∀ t, z t ≠ 0) (a : ℂ) (ha : Complex.exp a = z 0),
    ∃ f : ℝ → ℂ, Continuous f ∧ f 0 = a ∧ ∀ t, Complex.exp (f t) = z t := by
  exact BirkhoffGlobalSection.contact_angular_lift_bundle.1
