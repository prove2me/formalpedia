-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.eh_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:38:16.221439+00:00
-- url     : https://prove2.me/submissions/047671c9-8e91-42be-ba26-4a7b526caab6

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_hpart_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_rd_inv

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
theorem _root_.solution (Λ : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ) (v : Fin (2 * r + k + 1) → ℂ) (g : Mx k r)
    (p q : Fin (2 * r + k + 1)) :
    EH k r p q (fun y => Λ (y⁻¹ *ᵥ v)) g = -Λ ((Matrix.single p q 1 : Mx k r) *ᵥ (g⁻¹ *ᵥ v)) := by
  show RdV _ _ g + Complex.I • RdV _ _ g = _
  rw [rd_inv, rd_inv, smul_neg, ← neg_add, ← map_smul, ← map_add, ← Matrix.smul_mulVec, ← Matrix.add_mulVec,
    hpart_sum]
end Formalism.FourierDecayAlt.P.Qx5
