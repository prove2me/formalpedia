-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.lie_bracket
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:49:01.730125+00:00
-- url     : https://prove2.me/submissions/215e4241-52b1-4680-b279-771f16039756

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
open Qx2
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution {X Y : Mx k r} (hX : inLieLev k r i X) (hY : inLieLev k r i Y) :
    inLieLev k r i (X * Y - Y * X) := by
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · have hX' : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX.1
    have hY' : Yᴴ * Hpk k r = -(Hpk k r * Y) := eq_neg_of_add_eq_zero_left hY.1
    have e1 : Yᴴ * Xᴴ * Hpk k r = Hpk k r * Y * X := by
      rw [Matrix.mul_assoc, hX', Matrix.mul_neg, ← Matrix.mul_assoc, hY', Matrix.neg_mul, neg_neg]
    have e2 : Xᴴ * Yᴴ * Hpk k r = Hpk k r * X * Y := by
      rw [Matrix.mul_assoc, hY', Matrix.mul_neg, ← Matrix.mul_assoc, hX', Matrix.neg_mul, neg_neg]
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2,
      Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    abel
  · rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hX.2 a ha).1, (hY.2 a ha).1]
    simp
  · rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hX.2 a ha).2, (hY.2 a ha).2]
    simp
end Formalism.FourierDecayAlt.P.Qx5
