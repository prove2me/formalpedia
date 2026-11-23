-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.dual_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:57:45.89642+00:00
-- url     : https://prove2.me/submissions/dae128d6-8a40-4d42-ac21-67a4f60c78c3

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
open Formalism.DivisionValues.OperatorNormFrames
namespace Formalism.DivisionValues.OperatorNormFrames
theorem _root_.solution {K : Type} [Field K] {D : ℕ} (f : Module.Dual K (Fin D → K)) (e : Fin D → K) :
    f e = ∑ d, e d * f (Pi.single d 1) := by
  have he : e = ∑ d, e d • Pi.single d 1 := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [he]
  simp [map_sum, map_smul]
end Formalism.DivisionValues.OperatorNormFrames
