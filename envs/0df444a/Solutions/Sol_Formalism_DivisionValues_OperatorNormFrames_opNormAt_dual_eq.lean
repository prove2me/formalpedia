-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.opNormAt_dual_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:00.35081+00:00
-- url     : https://prove2.me/submissions/713c70d3-d650-4627-addd-181a59f165aa

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_toMatrix_dual

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] {a D : ℕ}
    (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (hE : ∀ v, IsUnit (XE v).det) (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K))
    (v : InfinitePlace K) :
    Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) XM (Pi.basisFun K (Fin D)).dualBasis
              (Formalism.HN.dualFrame XE) v B =
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((XE v)ᵀ * pmat v B * XM v))‖ := by
  simp only [Formalism.HN.opNormAt, Formalism.HN.dualFrame]
  rw [toMatrix_dual, Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hE v)]
end Formalism.DivisionValues.OperatorNormFrames
