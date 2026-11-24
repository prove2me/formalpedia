-- Prove2me | solution 1 for Formalism.L2.Th1.A.CubeR.formal_group_constCoeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:33:19.908091+00:00
-- url     : https://prove2.me/submissions/1f72f970-0e49-4ac5-900e-ed64be23dcea

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_hasSubst2
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_hasSubst2
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
open Formalism.L2.Th1.A.CubeR
open Univ CurveSer
local notation "cc" => MvPowerSeries.constantCoeff
variable {σ : Type*} {A : Type u} {B : Type v} [CommRing A] [CommRing B]
namespace Formalism.L2.Th1.A.CubeR
theorem _root_.solution (W : WeierstrassCurve A) {a b : MvPowerSeries σ A} (ha : cc a = 0) (hb : cc b = 0) :
    cc (MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ A) (fgl W)) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst2 ha hb) (Fin.forall_fin_two.2 ⟨ha, hb⟩)
    (Fgl1.fgl_cc W)
end Formalism.L2.Th1.A.CubeR
