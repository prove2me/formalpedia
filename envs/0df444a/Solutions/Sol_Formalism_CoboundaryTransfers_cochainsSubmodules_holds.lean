-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.cochainsSubmodules_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:54.041768+00:00
-- url     : https://prove2.me/submissions/9ee687e6-551b-446b-83d4-c724eb7f8763

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_qInv_of_mem
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_xN_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
namespace Formalism.CoboundaryTransfers
theorem _root_.solution : Submods := by
  intro O A _ _ _ B M D _ _ _ _ W
  exact ⟨⟨W.qInvSub, fun _ => Iff.rfl⟩, ⟨W.xNSub, fun _ => Iff.rfl⟩,
    ⟨W.twoCochains, fun _ => Iff.rfl⟩, ⟨W.cocycleSub, fun _ _ => Iff.rfl⟩,
    ⟨W.isCob1Sub, fun _ _ => Iff.rfl⟩, ⟨W.isCob2Sub, fun _ => Iff.rfl⟩,
    fun _ hn => W.qInv_of_mem hn, fun _ h => W.xN_mem h⟩
end Formalism.CoboundaryTransfers
