-- Prove2me | solution 1 for Formalism.L2.Th1.A.CubeR.yS_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:39.27561+00:00
-- url     : https://prove2.me/submissions/4f4e3ebb-a449-4b5f-b65c-4eb2968a1eed

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_neg


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
theorem _root_.solution (W : WeierstrassCurve A) {a : MvPowerSeries σ A} (ha : cc a = 0) :
    (yS W).subst a = -(xS W).subst a := by
  have hs : HasSubst a := HasSubst.of_constantCoeff_zero ha
  rw [yS, ← coe_substAlgHom hs, map_neg]
end Formalism.L2.Th1.A.CubeR
