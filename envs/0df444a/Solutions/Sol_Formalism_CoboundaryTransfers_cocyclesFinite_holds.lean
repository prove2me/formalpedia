-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.cocyclesFinite_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:57:12.414454+00:00
-- url     : https://prove2.me/submissions/06b6f368-7c56-4f2f-b189-2d7e7db84706

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_coboundaries_le_cocycles
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_finiteCocycles_le_cocycles
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_cocycle_mem_Zf
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_mem_coboundaries_of_isOneCoboundary

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
theorem _root_.solution : CocZf := by
  intro O A _ _ _ B M D _ _ _ _ W
  exact ⟨fun _ _ h => W.cocycle_mem_Zf h, W.coboundaries_le_cocycles, W.finiteCocycles_le_cocycles,
    fun _ _ h => W.mem_coboundaries_of_isOneCoboundary h⟩
end Formalism.CoboundaryTransfers
