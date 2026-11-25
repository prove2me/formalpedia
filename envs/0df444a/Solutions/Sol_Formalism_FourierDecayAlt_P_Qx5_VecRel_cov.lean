-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.VecRel.cov
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:29:03.002721+00:00
-- url     : https://prove2.me/submissions/af589b95-83ef-422e-b134-e81de6a2e7a0

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} {y : Fin n → A} {ξ : Fin n → ℂ} {ζb : A}
namespace Formalism.FourierDecayAlt.P.Qx5
namespace VecRel
theorem _root_.solution (h : VecRel E y ξ ζb) : CovRel (Eop E) y ξ ζb := by
  constructor
  · intro a b c
    have := h.Ey b a c
    simp only [Eop, neg_mul, mul_neg]
    rw [show -(E b a * y c) - -(y c * E b a) = -(E b a * y c - y c * E b a) by abel, this]
    split_ifs <;> simp
  · intro a b
    have := h.Eζ b a
    simp only [Eop, neg_mul, mul_neg]
    rw [show -(E b a * ζb) - -(ζb * E b a) = -(E b a * ζb - ζb * E b a) by abel, this, neg_neg]
end VecRel
end Formalism.FourierDecayAlt.P.Qx5
