-- Prove2me | solution 1 for Formalism.L2.Th1.A.ZSer.zSer_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:48:38.461239+00:00
-- url     : https://prove2.me/submissions/0ce40eb9-be54-411c-9c05-b6c4d43deed4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_SubstPairSubst
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_nSer_cc
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_zSer_negSucc
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_nSer_map
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_iSer


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
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
namespace Formalism.L2.Th1.A.ZSer
theorem _root_.solution {S : Type v} [CommRing S] (φ : R →+* S) (n : ℤ) :
    PowerSeries.map φ (zSer W n) = zSer (W.map φ) n := by
  rcases n with n | n
  · exact nSer_map W φ n
  · rw [zSer_negSucc, zSer_negSucc]
    refine (PowerSeries.map_subst (HasSubst.of_constantCoeff_zero' (nSer_cc W (n + 1))) (h := φ)
      (iSer W)).trans ?_
    rw [CurveSer.map_iSer]
    exact congrArg (fun t => PowerSeries.subst t (iSer (W.map φ))) (nSer_map W φ (n + 1))
end Formalism.L2.Th1.A.ZSer
