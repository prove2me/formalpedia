-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.lie_HXH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:50:24.898497+00:00
-- url     : https://prove2.me/submissions/df3c02ef-bff4-45e3-bc43-42c0d11dd60f

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx2_hpk_sq__e1ad91698796


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
theorem _root_.solution {X : Mx k r} (hX : inLieLev k r i X) : Hpk k r * Xᴴ * Hpk k r = -X := by
  have hX' : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX.1
  rw [Matrix.mul_assoc, hX', Matrix.mul_neg, ← Matrix.mul_assoc, hpk_sq', Matrix.one_mul]
end Formalism.FourierDecayAlt.P.Qx5
