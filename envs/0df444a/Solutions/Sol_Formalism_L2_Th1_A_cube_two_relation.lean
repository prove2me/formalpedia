-- Prove2me | solution 1 for Formalism.L2.Th1.A.cube_two_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:01:25.071664+00:00
-- url     : https://prove2.me/submissions/241fe5bb-d490-4fb5-a7ac-bd7b117c9c25

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_map_quadratic_lhs
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_map_diff2
import Theorems.Thm_Formalism_L2_Th1_A_CubeR_two_univ
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_fgl_map
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_neg
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_Univ_map_eq


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
open CubeR Univ
namespace Formalism.L2.Th1.A
theorem _root_.solution : CubeTwoR.{u} := by
  intro R _ W
  obtain ⟨c, hc, h⟩ := two_univ
  refine ⟨MvPowerSeries.map (φ_of W) c, ?_, ?_⟩
  · rw [MvPowerSeries.constantCoeff_map, hc, map_neg, map_one]
  · have := congrArg (MvPowerSeries.map (φ_of W)) h
    rw [map_mul, map_mul, map_quadratic_lhs, map_diff2, Fgl1.fgl_map, map_eq] at this
    exact this
end Formalism.L2.Th1.A
