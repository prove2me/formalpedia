-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.aC_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:24:52.33552+00:00
-- url     : https://prove2.me/submissions/72e2ff75-888a-4179-bf75-bb04798aa380

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_kc_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
open MeasureTheory Filter Topology
open Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution (g0 : Mat k r) (i : J k r) (Y W : J k r → ℝ) :
    aC g0 i Y W = kc i (-(fderiv ℝ (chart g0) Y W) * (chart g0 Y)⁻¹) := by
  have hW : W = ∑ b, W b • ebv b := pi_eq_sum_univ W
  have e1 : -(fderiv ℝ (chart g0) Y W) * (chart g0 Y)⁻¹ =
      ∑ b, W b • (-(fderiv ℝ (chart g0) Y (ebv b)) * (chart g0 Y)⁻¹) := by
    conv_lhs => rw [hW]
    rw [map_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, ← smul_neg, Matrix.smul_mul]
  rw [e1, kc_sum]
  simp only [aC, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, sC]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _
end Formalism.FourierDecayAlt.P.Ux10
