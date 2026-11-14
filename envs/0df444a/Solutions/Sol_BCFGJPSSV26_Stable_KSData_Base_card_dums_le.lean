-- Prove2me | solution 1 for BCFGJPSSV26.Stable.KSData.Base.card_dums_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:08:15.907109+00:00
-- url     : https://prove2.me/submissions/bdfea36d-e971-4602-8270-4ce2c216f18e

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingGhost
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingBridge
import all Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingBridge
public import Theorems.Thm_BCFGJPSSV26_Stable_Hyp_card_O1_le

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace KSData

variable (K : KSData)

theorem card_OO_le : K.OO.card ≤ K.X.s :=
  (card_le_card fun _ hc ↦ K.w₁.O2_subset (mem_sdiff.1 hc).1).trans K.H.card_O1_le

section

variable {K}

theorem Base.card_dums_le {del : List ℕ} {D : List DumQ} (hb : K.Base del D) :
    D.length ≤ K.X.s := by
  rw [← hb.card]
  exact (card_le_card (K.matched_subset D)).trans K.card_OO_le

end

section

variable {K}

end

end KSData

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.KSData.Base.card_dums_le := @BCFGJPSSV26.Stable.KSData.Base.card_dums_le
