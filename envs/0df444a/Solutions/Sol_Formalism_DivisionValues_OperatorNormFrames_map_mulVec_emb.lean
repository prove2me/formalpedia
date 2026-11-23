-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.map_mulVec_emb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:17.769088+00:00
-- url     : https://prove2.me/submissions/4d21deca-8563-49ef-8385-433586f0209e

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
variable {K : Type} [Field K] [NumberField K] {D : ℕ}
namespace Formalism.DivisionValues.OperatorNormFrames
theorem _root_.solution {n : ℕ} (v : InfinitePlace K) (N : Matrix (Fin D) (Fin n) K) (x : Fin n → K) :
    (fun i => v.embedding (N.mulVec x i)) = (N.map v.embedding).mulVec fun i => v.embedding (x i) := by
  ext i
  first
    | simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    | simp [Matrix.mulVec, Matrix.dotProduct, map_sum, map_mul]
end Formalism.DivisionValues.OperatorNormFrames
