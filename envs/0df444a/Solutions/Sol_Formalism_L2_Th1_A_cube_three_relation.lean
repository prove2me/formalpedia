-- Prove2me | solution 1 for Formalism.L2.Th1.A.cube_three_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:22:34.643489+00:00
-- url     : https://prove2.me/submissions/e6e2897f-5d69-43b7-a1b0-7993234b5843

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_map_cubic_lhs
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_map_cubic_sum
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_three_univ
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_neg
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_Univ_map_eq
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
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
open CubeR Univ
namespace Formalism.L2.Th1.A
theorem _root_.solution : CubeThreeR.{u} := by
  intro R _ W t row
  obtain ⟨e, he, h⟩ := three_univ
  refine ⟨MvPowerSeries.map (φ_of W) e, ?_, ?_⟩
  · rw [MvPowerSeries.constantCoeff_map, he, map_neg, map_one]
  · have := congrArg (MvPowerSeries.map (φ_of W)) h
    simp only [map_mul, map_sub, map_cubic_lhs, map_cubic_sum, MvPowerSeries.map_X, map_eq] at this
    exact this
end Formalism.L2.Th1.A
