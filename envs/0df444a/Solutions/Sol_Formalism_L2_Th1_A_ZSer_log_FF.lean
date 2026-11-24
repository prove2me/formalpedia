-- Prove2me | solution 1 for Formalism.L2.Th1.A.ZSer.log_FF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:33:18.547814+00:00
-- url     : https://prove2.me/submissions/9ecadfd7-7571-42f8-a71c-bdbcfc3c7452

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_SubstPairSubst
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_hasSubst_pair
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_subst_pair_subst
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_fgl_cc


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
theorem _root_.solution (hL : FglLog.{u}) {a b : K⟦X⟧} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) :
    (logSer W).subst (FF[W](a, b)) = (logSer W).subst a + (logSer W).subst b := by
  have hab := hasSubst_pair ha hb
  have e := congrArg (MvPowerSeries.subst (![a, b] : Fin 2 → K⟦X⟧)) (hL K W).1
  rw [subst_pair_subst ha hb (Fgl1.fgl_cc W), MvPowerSeries.subst_add hab,
    subst_pair_subst ha hb (MvPowerSeries.constantCoeff_X 0),
    subst_pair_subst ha hb (MvPowerSeries.constantCoeff_X 1),
    MvPowerSeries.subst_X hab, MvPowerSeries.subst_X hab] at e
  exact e
end Formalism.L2.Th1.A.ZSer
