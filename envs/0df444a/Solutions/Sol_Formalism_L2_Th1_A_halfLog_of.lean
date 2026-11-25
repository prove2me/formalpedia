-- Prove2me | solution 1 for Formalism.L2.Th1.A.halfLog_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:48:22.336828+00:00
-- url     : https://prove2.me/submissions/f8e8afe0-e88c-4648-a9f5-4ac69ba641d9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_SubstPairSubst
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_subst_C_mul
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_nSer_cc
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_nSer_map
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_log_nSer
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_nSer_two_coeff
import Theorems.Thm_Formalism_L2_Th1_A_halfSpec_of
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_composition_inverse_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
namespace Formalism.L2.Th1.A
theorem _root_.solution (hL : FglLog.{u}) (hL0 : FglLog.{0}) : HalfLog.{u, v} := by
  refine ⟨fun K _ _ W => ?_, fun R S _ _ φ W h2 => ?_⟩
  · obtain ⟨hh0, -, hsh, -, -⟩ := halfSpec_of hL0 K W (isUnit_iff_ne_zero.mpr two_ne_zero)
    have hh := HasSubst.of_constantCoeff_zero' hh0
    have hX : (logSer W).subst (X : K⟦X⟧) = logSer W := by
      rw [← PowerSeries.map_algebraMap_eq_subst_X]
      rfl
    have e2 : PowerSeries.subst (halfSer W) ((logSer W).subst (nSer W 2)) = logSer W := by
      rw [PowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' (ZSer.nSer_cc W 2)) hh, hsh, hX]
    rw [ZSer.log_nSer W hL 2, ZSer.subst_C_mul hh, Nat.cast_ofNat, map_ofNat] at e2
    exact e2
  · have hc : coeff 1 (nSer W 2) = 2 := ZSer.nSer_two_coeff W hL0
    have hu : IsUnit (coeff 1 (nSer W 2)) := by
      rw [hc]
      exact h2
    show PowerSeries.map φ (compInv (nSer W 2)) = compInv (nSer (W.map φ) 2)
    rw [composition_inverse_map R S φ (nSer W 2) (ZSer.nSer_cc W 2) hu, ZSer.nSer_map]
end Formalism.L2.Th1.A
