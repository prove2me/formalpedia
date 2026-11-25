-- Prove2me | solution 1 for Formalism.L2.Th1.A.ZSer.field_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:28:00.129666+00:00
-- url     : https://prove2.me/submissions/030c4e4a-8c27-4622-9eb5-1c66586fcbeb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_SubstPairSubst
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_FF_cc
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_zSer_cc
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_log_inj
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_log_FF
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_log_zSer
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add


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
    FF[W](zSer W m, zSer W n) = zSer W (m + n) := by
  apply log_inj W (FF_cc W (zSer_cc W m) (zSer_cc W n)) (zSer_cc W (m + n))
  rw [log_FF W hL (zSer_cc W m) (zSer_cc W n), log_zSer W hL m, log_zSer W hL n, log_zSer W hL (m + n),
    Int.cast_add, map_add, add_mul]
end Formalism.L2.Th1.A.ZSer
