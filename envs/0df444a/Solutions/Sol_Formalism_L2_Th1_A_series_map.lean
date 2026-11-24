-- Prove2me | solution 1 for Formalism.L2.Th1.A.series_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:45:37.666408+00:00
-- url     : https://prove2.me/submissions/b3dcf2d4-b207-4b85-981e-4beee45fcd79

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_wSer
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_wU
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_xS
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_yS
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_fw
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_fu
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_om
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
open CurveSer
namespace Formalism.L2.Th1.A
theorem _root_.solution : SeriesMap.{u, v} := by
  unfold SeriesMap
  intro R S _ _ φ W
  exact ⟨map_wSer W φ, map_wU W φ, map_xS W φ, map_yS W φ, map_fw W φ, map_fu W φ, map_om W φ,
    map_iSer W φ⟩
end Formalism.L2.Th1.A
