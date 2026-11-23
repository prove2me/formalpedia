-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.dot_frames
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:17.273088+00:00
-- url     : https://prove2.me/submissions/41d732e0-573d-4622-b95e-606513dce224

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
open Formalism.DivisionValues.OperatorNormFrames
namespace Formalism.DivisionValues.OperatorNormFrames
theorem _root_.solution {a D : ℕ} (Y : Matrix (Fin D) (Fin D) ℂ) (M : Matrix (Fin D) (Fin a) ℂ)
    (X : Matrix (Fin a) (Fin a) ℂ) (x : Fin a → ℂ) (y : Fin D → ℂ) :
    y ⬝ᵥ (Yᵀ * M * X).mulVec x = (Y.mulVec y) ⬝ᵥ M.mulVec (X.mulVec x) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
end Formalism.DivisionValues.OperatorNormFrames
