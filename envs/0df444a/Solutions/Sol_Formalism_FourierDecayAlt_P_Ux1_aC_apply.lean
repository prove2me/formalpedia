-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.aC_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:17:24.741797+00:00
-- url     : https://prove2.me/submissions/3e235612-1f47-4bb8-b06f-1b7b6eae94ab

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_kc_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux1
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
end Formalism.FourierDecayAlt.P.Ux1
