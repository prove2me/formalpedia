-- Prove2me | solution 1 for Formalism.L2.Th1.A.CubeR.map_quadratic_lhs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:44:20.00058+00:00
-- url     : https://prove2.me/submissions/409ec1b8-1213-497d-8e68-3bc99fbaf09d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_xS
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub


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
theorem _root_.solution (φ : A →+* B) : MvPowerSeries.map φ (lhs2 W) = lhs2 (W.map φ) := by
  unfold lhs2
  rw [map_sub, map_mul, map_mul, map_pow, map_pow, PowerSeries.map_subst (HasSubst.X 0),
    PowerSeries.map_subst (HasSubst.X 1), map_xS, MvPowerSeries.map_X, MvPowerSeries.map_X]
end Formalism.L2.Th1.A.CubeR
