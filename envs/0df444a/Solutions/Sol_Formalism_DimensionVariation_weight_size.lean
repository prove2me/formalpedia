-- Prove2me | solution 1 for Formalism.DimensionVariation.weight_size
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:18.05729+00:00
-- url     : https://prove2.me/submissions/18c311a2-34e6-4749-9e62-ac5fe2ea5ece

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqExplicit6
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
namespace Formalism.DimensionVariation
theorem _root_.solution : WeightSize6 := by
  intro k m t N S Sc w η hk hm ht hN hS hSc
  have h1 : (k - 1) * S ≤ k * Sc := by nlinarith
  have hmt : 0 ≤ m * (t + 1) := by positivity
  have h2 : (k - 1) * (N + t + 1) ≤ (N + t) ^ 2 := by
    have a1 : k - 1 ≤ N + t - 1 := by linarith
    have a2 : 0 ≤ N + t + 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right a1 a2]
  nlinarith
end Formalism.DimensionVariation
