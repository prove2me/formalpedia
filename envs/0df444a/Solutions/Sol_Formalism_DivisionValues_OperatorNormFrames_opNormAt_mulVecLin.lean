-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.opNormAt_mulVecLin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:58.48942+00:00
-- url     : https://prove2.me/submissions/069bcc5f-9fe5-4a28-9df3-15c25a569cae

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] {a b : ℕ}
    (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (X' : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ)
    (v : InfinitePlace K) (N : Matrix (Fin b) (Fin a) K) :
    Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) X (Pi.basisFun K (Fin b)) X' v (Matrix.mulVecLin N) =
      nrm ((X' v)⁻¹ * N.map v.embedding * X v) := by
  have hN : LinearMap.toMatrix (Pi.basisFun K (Fin a)) (Pi.basisFun K (Fin b)) (Matrix.mulVecLin N) = N := by
    ext i j
    simp [LinearMap.toMatrix_apply]
  simp only [Formalism.HN.opNormAt, nrm, hN]
end Formalism.DivisionValues.OperatorNormFrames
