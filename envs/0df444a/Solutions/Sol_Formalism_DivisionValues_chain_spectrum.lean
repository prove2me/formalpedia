-- Prove2me | solution 1 for Formalism.DivisionValues.chain_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:14.58506+00:00
-- url     : https://prove2.me/submissions/0de6eb76-6914-439b-a536-e80e70d2b7f8

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm

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
namespace Formalism.DivisionValues
theorem _root_.solution : ChainSpec := by
  unfold ChainSpec
  refine ⟨fun m C Kj φ => ⟨?_, fun j => ?_⟩, fun R _ m c Kj => ⟨?_, fun j => ?_⟩⟩
  · first | rfl | simp [chainFun]
  · first | rfl | simp [chainFun]
  · first | rfl | simp [chainMat]
  · first | rfl | simp [chainMat]
end Formalism.DivisionValues
