-- Prove2me | solution 1 for BCFGJPSSV26.Stable.KSData.Base.card_add_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:13:13.312345+00:00
-- url     : https://prove2.me/submissions/defa1071-81a3-4277-bc8d-d345fdd4f43c

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingGhost
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingBridge
import all Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingBridge
public import Theorems.Thm_BCFGJPSSV26_Stable_KSData_Base_card_del_le
public import Theorems.Thm_BCFGJPSSV26_Stable_KSData_Base_card_dums_le

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace KSData

variable (K : KSData)

section

variable {K}

theorem Base.card_add_le {del : List ℕ} {D : List DumQ} (hb : K.Base del D) :
    D.length + del.length ≤ 2 * K.X.s := by
  have := hb.card_dums_le
  have := hb.card_del_le
  omega

end

section

variable {K}

end

end KSData

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.KSData.Base.card_add_le := @BCFGJPSSV26.Stable.KSData.Base.card_add_le
