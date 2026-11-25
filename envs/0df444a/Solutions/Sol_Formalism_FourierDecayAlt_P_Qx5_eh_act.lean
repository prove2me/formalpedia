-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.eh_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:06:51.766946+00:00
-- url     : https://prove2.me/submissions/b3e2f532-f006-4b2d-9fc3-011368009223

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_eh_linear
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx5_single_mulVec__ad7365b648dd

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
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution (Λ : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ) (u : Fin (2 * r + k + 1) → ℂ) (g : Mx k r)
    (p q : Fin (2 * r + k + 1)) : EH k r p q (fun y => Λ (y *ᵥ u)) g = u q * Λ (g *ᵥ bvec p) := by
  have h := eh_linear (actL Λ u) g p q
  have e : actL Λ u (g * Matrix.single p q 1) = u q * Λ (g *ᵥ bvec p) := by
    show Λ ((g * Matrix.single p q 1) *ᵥ u) = _
    rw [← Matrix.mulVec_mulVec, single_mulVec', Matrix.mulVec_smul, map_smul, smul_eq_mul]
  rw [← e, ← h]
  rfl
end Formalism.FourierDecayAlt.P.Qx5
