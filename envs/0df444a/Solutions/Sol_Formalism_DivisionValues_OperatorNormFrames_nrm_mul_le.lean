-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.nrm_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:19.374048+00:00
-- url     : https://prove2.me/submissions/3465f9c8-80ed-4fa7-b52e-008dcd39122a

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
theorem _root_.solution {a b c : ℕ} (A : Matrix (Fin c) (Fin b) ℂ) (B : Matrix (Fin b) (Fin a) ℂ) :
    nrm (A * B) ≤ nrm A * nrm B := by
  unfold nrm
  have e : LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (A * B)) =
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)).comp
        (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B)) := by
    ext x : 1
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
  rw [e]
  exact ContinuousLinearMap.opNorm_comp_le _ _
end Formalism.DivisionValues.OperatorNormFrames
