-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl2.inv_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:14:50.830789+00:00
-- url     : https://prove2.me/submissions/aaca487f-77c3-4a36-b1e7-4f94de82bb61

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowThird
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalLogarithmBaseChange
import Theorems.Thm_Formalism_L2_Th1_A_Fgl2_hasSubst_X_iSer
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_iSer
import Theorems.Thm_Formalism_L2_Th1_A_formal_group_map


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
open Formalism.L2.Th1.A.Fgl2
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
namespace Formalism.L2.Th1.A.Fgl2
theorem _root_.solution {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S)
    (W : WeierstrassCurve R) :
    PowerSeries.map φ (MvPowerSeries.subst (![X, iSer W] : Fin 2 → R⟦X⟧) (fgl W))
      = MvPowerSeries.subst (![X, iSer (W.map φ)] : Fin 2 → S⟦X⟧) (fgl (W.map φ)) := by
  have h := MvPowerSeries.map_subst (h := φ) (hasSubst_X_iSer W) (fgl W)
  change MvPowerSeries.map φ _ = _
  rw [h, formal_group_map R S φ W]
  congr 1
  funext i
  fin_cases i
  · exact PowerSeries.map_X _
  · exact CurveSer.map_iSer (φ := φ) (W := W)
end Formalism.L2.Th1.A.Fgl2
