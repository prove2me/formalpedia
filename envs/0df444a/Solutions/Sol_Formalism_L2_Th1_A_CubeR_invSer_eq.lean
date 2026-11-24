-- Prove2me | solution 1 for Formalism.L2.Th1.A.CubeR.invSer_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:19:17.376261+00:00
-- url     : https://prove2.me/submissions/43f99bc5-e18a-45d9-b6ea-7f41b1fae422

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_iDen_cc


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
theorem _root_.solution {K : Type u} [Field K] (W : WeierstrassCurve K) :
    Formalism.ELL.invSer W (wSer W) = iSer W := by
  unfold Formalism.ELL.invSer iSer
  rw [PowerSeries.invOfUnit_eq' (iDen W) (-1) (by rw [iDen_cc, Units.val_neg, Units.val_one])]
  rfl
end Formalism.L2.Th1.A.CubeR
