-- Prove2me | solution 1 for Formalism.DivisionValues.quotient_metric_representation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:43.390799+00:00
-- url     : https://prove2.me/submissions/63811b53-e6ee-4f9d-9ddb-c98f7926f6eb

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_quot_rep
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_quot_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open OperatorNormFrames
open OperatorNormFrames
namespace Formalism.DivisionValues
theorem _root_.solution : QuotMetricRep := by
  unfold QuotMetricRep
  intro K _ _ _ n D H X0 h0 P hP XQ hQ v
  obtain ⟨hQu, hQe⟩ := hQ v
  exact ⟨fun x => quot_le (H.map v.embedding) (X0 v) (h0 v).1 (h0 v).2 (P.map v.embedding) (XQ v)
      hQu hQe x,
    fun y => quot_rep (H.map v.embedding) (X0 v) (h0 v).1 (h0 v).2 (P.map v.embedding) (XQ v)
      hQu hQe y⟩
end Formalism.DivisionValues
