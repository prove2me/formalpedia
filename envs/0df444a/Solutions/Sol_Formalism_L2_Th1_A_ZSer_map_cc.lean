-- Prove2me | solution 1 for Formalism.L2.Th1.A.ZSer.map_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:13:38.498783+00:00
-- url     : https://prove2.me/submissions/9304ec38-554c-4356-b94f-08d0fb9acd6c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_SubstPairSubst

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
variable {R : Type u} [CommRing R]
namespace Formalism.L2.Th1.A.ZSer
theorem _root_.solution {S : Type v} [CommRing S] (φ : R →+* S) {a : R⟦X⟧} (ha : constantCoeff a = 0) :
    constantCoeff (PowerSeries.map φ a) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, ha, map_zero]
end Formalism.L2.Th1.A.ZSer
