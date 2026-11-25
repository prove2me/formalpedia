-- Prove2me | solution 1 for Formalism.L2.Th1.A.ZSer.field_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:28:01.946715+00:00
-- url     : https://prove2.me/submissions/a5bbcd38-dd81-4ba4-93f7-a3e6324e4ff7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_SubstPairSubst
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_subst_C_mul
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_cc_subst
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_zSer_cc
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_log_inj
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_log_zSer
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul


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
open Formalism.L2.Th1.A.ZSer
local notation "FF[" W "](" a ", " b ")" =>
  MvPowerSeries.subst (![a, b] : Fin 2 → PowerSeries _) (fgl W)
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
namespace Formalism.L2.Th1.A.ZSer
theorem _root_.solution (hL : FglLog.{u}) (m n : ℤ) :
    (zSer W m).subst (zSer W n) = zSer W (m * n) := by
  have hm := HasSubst.of_constantCoeff_zero (zSer_cc W m)
  have hn := HasSubst.of_constantCoeff_zero (zSer_cc W n)
  have hcc : constantCoeff ((zSer W m).subst (zSer W n)) = 0 := by
    rw [cc_subst (zSer_cc W n)]
    exact zSer_cc W m
  apply log_inj W hcc (zSer_cc W (m * n))
  rw [← PowerSeries.subst_comp_subst_apply hm hn, log_zSer W hL m, subst_C_mul hn, log_zSer W hL n,
    log_zSer W hL (m * n), Int.cast_mul, map_mul, mul_assoc]
end Formalism.L2.Th1.A.ZSer
