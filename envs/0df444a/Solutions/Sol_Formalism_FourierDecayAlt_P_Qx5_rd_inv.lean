-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.rd_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:04:48.482874+00:00
-- url     : https://prove2.me/submissions/4a4e5961-784c-4d49-bf6f-a4cab7863f3e

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_rd_linear
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_exp_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


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
theorem _root_.solution (Λ : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ) (v : Fin (2 * r + k + 1) → ℂ) (g X : Mx k r) :
    RdV X (fun y => Λ (y⁻¹ *ᵥ v)) g = -Λ (X *ᵥ (g⁻¹ *ᵥ v)) := by
  have h := rd_linear (actL Λ (g⁻¹ *ᵥ v)) 1 (-X)
  have e : RdV X (fun y => Λ (y⁻¹ *ᵥ v)) g = RdV (-X) (fun y => actL Λ (g⁻¹ *ᵥ v) y) 1 := by
    unfold RdV
    congr 1
    funext t
    show Λ ((g * NormedSpace.exp ((t : ℂ) • X))⁻¹ *ᵥ v) = Λ ((1 * NormedSpace.exp ((t : ℂ) • (-X))) *ᵥ (g⁻¹ *ᵥ v))
    rw [Matrix.mul_inv_rev, exp_inv, Matrix.one_mul, Matrix.mulVec_mulVec]
  rw [e, h]
  show Λ ((1 * -X) *ᵥ (g⁻¹ *ᵥ v)) = _
  rw [Matrix.one_mul, Matrix.neg_mulVec, map_neg]
end Formalism.FourierDecayAlt.P.Qx5
