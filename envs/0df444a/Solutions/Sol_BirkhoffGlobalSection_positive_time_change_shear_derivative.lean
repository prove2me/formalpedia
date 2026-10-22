-- Prove2me | solution 1 for BirkhoffGlobalSection.positive_time_change_shear_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T21:13:24.225246+00:00
-- url     : https://prove2.me/submissions/4ed85bad-bb7f-4374-a917-3a2f3a5d7d97

import Theorems.Thm_BirkhoffGlobalSection_positive_time_change_bundle
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution :
∀ (r k l : ℝ → ℝ) (hr : Continuous r) (hk : Continuous k)
    (hpos : ∀ t, 0 < r t) (hdr : ∀ t, HasDerivAt r (r t * l t) t),
    let η : ℝ → ℝ := fun t => r t * ∫ s in (0 : ℝ)..t, k s / r s
    η 0 = 0 ∧ ∀ t, HasDerivAt η (k t + η t * l t) t := by
  exact BirkhoffGlobalSection.positive_time_change_bundle.{0, 0}.2.1
