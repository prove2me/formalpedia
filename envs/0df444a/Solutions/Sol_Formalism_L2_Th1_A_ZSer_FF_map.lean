-- Prove2me | solution 1 for Formalism.L2.Th1.A.ZSer.FF_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:13:28.876775+00:00
-- url     : https://prove2.me/submissions/ba70ec19-8af4-466c-bf4c-490db8fca9ff

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_SubstPairSubst
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_map_subst_pair
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_fgl_map


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
theorem _root_.solution {S : Type v} [CommRing S] (φ : R →+* S) {a b : R⟦X⟧}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    PowerSeries.map φ (FF[W](a, b)) = FF[W.map φ](PowerSeries.map φ a, PowerSeries.map φ b) := by
  rw [map_subst_pair φ ha hb, Fgl1.fgl_map W φ]
end Formalism.L2.Th1.A.ZSer
