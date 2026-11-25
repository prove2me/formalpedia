-- Prove2me | solution 1 for Formalism.L2.Th1.E.ScaledModelNorms.dwp_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:51:39.905327+00:00
-- url     : https://prove2.me/submissions/65210fed-feb7-474f-a719-91f7523b0f85

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CubeThreeR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_CmIntegralityOfTorsionPoints
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_F_Homog_tsum_scale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.ScaledModelNorms
open Formalism.L2.Th1
namespace Formalism.L2.Th1.E.ScaledModelNorms
theorem _root_.solution (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    (F.scalePair L c hc).derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * L.derivWeierstrassP z := by
  have h := F.Homog.tsum_scale L c hc (fun w => -2 / (c * z - w) ^ 3)
  rw [← (PeriodPair.hasSum_derivWeierstrassP _ (c * z)).tsum_eq,
    ← (PeriodPair.hasSum_derivWeierstrassP L z).tsum_eq, h, ← tsum_mul_left]
  congr 1
  funext w
  rw [← mul_sub, mul_pow]
  simp only [div_eq_mul_inv, mul_inv]
  ring
end Formalism.L2.Th1.E.ScaledModelNorms
