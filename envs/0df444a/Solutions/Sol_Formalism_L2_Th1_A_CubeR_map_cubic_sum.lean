-- Prove2me | solution 1 for Formalism.L2.Th1.A.CubeR.map_cubic_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:28:48.594812+00:00
-- url     : https://prove2.me/submissions/ca26d445-04c6-4704-936c-55573105ffa5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_map_formal_group_subst
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_formal_group_constCoeff_zero

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
theorem _root_.solution (φ : A →+* B) : MvPowerSeries.map φ (sum3 W) = sum3 (W.map φ) := by
  unfold sum3
  rw [map_formal_group_subst φ W (formal_group_constCoeff_zero W (MvPowerSeries.constantCoeff_X 0) (MvPowerSeries.constantCoeff_X 1))
    (MvPowerSeries.constantCoeff_X 2),
    map_formal_group_subst φ W (MvPowerSeries.constantCoeff_X 0) (MvPowerSeries.constantCoeff_X 1),
    MvPowerSeries.map_X, MvPowerSeries.map_X, MvPowerSeries.map_X]
end Formalism.L2.Th1.A.CubeR
