-- Prove2me | solution 1 for Formalism.L2.Th1.A.CubeR.two_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:45:16.210143+00:00
-- url     : https://prove2.me/submissions/6e33bc87-82e9-4520-a1c6-ea3feddacb9f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_inv_wU_subst
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_invSer_eq
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_lift
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_lift_cc
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_map_quadratic_lhs
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_map_diff2
import Theorems.Thm_Formalism_ELL_cubeTwo
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_wSer_fixed
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_fgl_cc
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_fgl_map
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_wSer_fixed
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_Univ_mv_map_injective
import Theorems.Thm_Formalism_L2_Th1_A_fglSum
import Theorems.Thm_P2M_Formalism_L2_Th1_A_Univ___injective_04fee711be81


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
theorem _root_.solution : ∃ c : MvPowerSeries (Fin 2) Z, cc c = -1 ∧ lhs2 W₀ = c * fgl W₀ * diff2 W₀ := by
  obtain ⟨c, hc, hc0, h⟩ := Formalism.ELL.cubeTwo K₀ WK (wSer WK) (fgl WK) (wSer_fixed WK)
    (Fgl1.fgl_cc WK) (fglSum K₀ WK)
  obtain ⟨c₀, rfl⟩ := lift c hc
  refine ⟨c₀, lift_cc hc0, mv_map_injective ι ι_injective ?_⟩
  rw [inv_wU_subst WK (MvPowerSeries.constantCoeff_X 0),
    inv_wU_subst WK (MvPowerSeries.constantCoeff_X 1), invSer_eq] at h
  rw [map_mul, map_mul, map_quadratic_lhs, map_diff2, Fgl1.fgl_map]
  exact h
end Formalism.L2.Th1.A.CubeR
