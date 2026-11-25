-- Prove2me | solution 1 for Formalism.L2.Th1.A.CubeR.three_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:16:27.972914+00:00
-- url     : https://prove2.me/submissions/588908dd-aad9-446f-b91c-fd7b172be5b2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_inv_wU_subst
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_yS_subst
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_lift
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_lift_cc
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_map_cubic_lhs
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_map_cubic_sum
import Theorems.Thm_Formalism_ELL_cubeThree
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_wSer_fixed
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_fgl_cc
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_wSer_fixed
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_Univ_mv_map_injective
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_fglSum
import Theorems.Thm_P2M_Formalism_L2_Th1_A_Univ___injective_04fee711be81
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



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
theorem _root_.solution : ∃ e : MvPowerSeries (Fin 3) Z, cc e = -1 ∧
    lhs3 W₀ = e * sum3 W₀ * (MvPowerSeries.X 0 - MvPowerSeries.X 1)
      * (MvPowerSeries.X 0 - MvPowerSeries.X 2) * (MvPowerSeries.X 1 - MvPowerSeries.X 2) := by
  obtain ⟨e, he, he0, h⟩ := Formalism.ELL.cubeThree K₀ WK (wSer WK) (fgl WK) (wSer_fixed WK)
    (Fgl1.fgl_cc WK) (fglSum K₀ WK)
  obtain ⟨e₀, rfl⟩ := lift e he
  refine ⟨e₀, lift_cc he0, mv_map_injective ι ι_injective ?_⟩
  simp only [inv_wU_subst WK (MvPowerSeries.constantCoeff_X _)] at h
  simp only [map_mul, map_sub, map_cubic_lhs, map_cubic_sum, MvPowerSeries.map_X]
  unfold lhs3
  simp only [yS_subst _ (MvPowerSeries.constantCoeff_X _)]
  exact h
end Formalism.L2.Th1.A.CubeR
