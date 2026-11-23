-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.mul_inv_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:00:11.874722+00:00
-- url     : https://prove2.me/submissions/4f7a7477-90da-4984-ac3e-5f1e3c5fb1c8

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
theorem _root_.solution {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : IsUnit Y.det) (x : Fin n → ℂ) :
    Y.mulVec (Y⁻¹.mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hY, Matrix.one_mulVec]
end Formalism.DivisionValues.OperatorNormFrames
