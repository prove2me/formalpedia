-- Prove2me | solution 1 for Formalism.DimensionVariation.flat_line_degree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:01.655787+00:00
-- url     : https://prove2.me/submissions/04eb71bf-9260-488c-a619-6e4a41b24bae

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
theorem _root_.solution : FlatLineDegree6 := by
  intro p q' logOm lrdK lrdE dfl c1 hq hK hKE hd hc
  have e2 : c1 + (p - q') * logOm / 2 = -(q' * (2 * lrdK - lrdE)) := by rw [hc, hd]; ring
  have e3 : |2 * lrdK - lrdE| ≤ lrdE := abs_le.mpr ⟨by linarith, by linarith⟩
  refine ⟨by rw [hd]; ring, e2, e3, ?_⟩
  rw [e2, abs_neg, abs_mul, abs_of_nonneg hq]
  exact mul_le_mul_of_nonneg_left e3 hq
end Formalism.DimensionVariation
