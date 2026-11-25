-- Prove2me | solution 1 for Formalism.L2.Th1.A.z_series_map_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:04:35.527648+00:00
-- url     : https://prove2.me/submissions/0fc66000-1c9a-485f-af55-262d7bdb1bca

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementM
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ChainRuleFormalGroupVar
import Theorems.Thm_Formalism_L2_Th1_A_More_map_logSer
import Theorems.Thm_P2M_Formalism_L2_Th1_A_More_map_g__846035df1560
import Theorems.Thm_P2M_Formalism_L2_Th1_A_More_map_g__04ce263af0ef
import Theorems.Thm_Formalism_L2_Th1_A_More_map_cleared
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_cleared_unique
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_wpL_shape
import Theorems.Thm_Formalism_L2_Th1_A_compInvMap
import Theorems.Thm_Formalism_L2_Th1_A_expSpec
import Theorems.Thm_Formalism_L2_Th1_A_logSpec
import Theorems.Thm_Formalism_L2_Th1_A_wpODE


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
open More
namespace Formalism.L2.Th1.A
theorem _root_.solution : ZMap.{u, v} := by
  intro K L _ _ _ _ φ W
  obtain ⟨l0, l1, -⟩ := logSpec K W
  refine ⟨map_logSer φ W, ?_, ?_, map_g₂ φ W, map_g₃ φ W⟩
  · rw [expSer, compInvMap K L φ (logSer W) l0 (by rw [l1]; exact isUnit_one), map_logSer, expSer]
  · have h1 := map_cleared φ (WpSh.wpL_shape expSpec wpODE W).2
    rw [map_g₂, map_g₃] at h1
    exact WpSh.cleared_unique h1 (WpSh.wpL_shape expSpec wpODE (W.map φ)).2
end Formalism.L2.Th1.A
