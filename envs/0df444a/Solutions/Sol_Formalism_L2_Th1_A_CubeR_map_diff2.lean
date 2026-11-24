-- Prove2me | solution 1 for Formalism.L2.Th1.A.CubeR.map_diff2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:28:49.236269+00:00
-- url     : https://prove2.me/submissions/aba1bf44-fdb0-4923-91f4-ed4083493f8c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_map_formal_group_subst
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_iSer_subst_cc
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
open Formalism.L2.Th1.A.CubeR
open Univ CurveSer
local notation "cc" => MvPowerSeries.constantCoeff
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] (W : WeierstrassCurve A)
namespace Formalism.L2.Th1.A.CubeR
theorem _root_.solution (φ : A →+* B) : MvPowerSeries.map φ (diff2 W) = diff2 (W.map φ) := by
  unfold diff2
  rw [map_formal_group_subst φ W (MvPowerSeries.constantCoeff_X 0)
    (iSer_subst_cc W (MvPowerSeries.constantCoeff_X 1)), PowerSeries.map_subst (HasSubst.X 1),
    map_iSer, MvPowerSeries.map_X, MvPowerSeries.map_X]
end Formalism.L2.Th1.A.CubeR
