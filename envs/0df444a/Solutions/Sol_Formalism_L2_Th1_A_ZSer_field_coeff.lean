-- Prove2me | solution 1 for Formalism.L2.Th1.A.ZSer.field_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:28:01.000832+00:00
-- url     : https://prove2.me/submissions/e3d9b038-40d1-475c-ac8c-dd9f26916183

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_SubstPairSubst
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_coeff_one_subst
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_zSer_cc
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_log_one
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_log_zSer
import Theorems.Thm_Formalism_ELL_FormalGroupLinearJets_coeff_one_subst


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
theorem _root_.solution (hL : FglLog.{u}) (n : ℤ) : coeff 1 (zSer W n) = (n : K) := by
  have h := congrArg (coeff 1) (log_zSer W hL n)
  rw [coeff_one_subst (zSer_cc W n), log_one, one_mul, coeff_C_mul, log_one, mul_one] at h
  exact h
end Formalism.L2.Th1.A.ZSer
