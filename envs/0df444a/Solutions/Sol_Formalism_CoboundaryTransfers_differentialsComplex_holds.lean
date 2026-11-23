-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.differentialsComplex_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:45.219861+00:00
-- url     : https://prove2.me/submissions/0e768e4a-c916-4048-8040-8497044ea561

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_diffOne_diffZero
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_isOneCochain_diffZero
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_isTwoCochain_diffOne
import Theorems.Thm_Formalism_CoboundaryTransfers_WachMod_cocycle_of_isCob1

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
theorem _root_.solution : Complex := by
  intro O A _ _ _ B M D _ _ _ _ W
  exact ⟨fun _ hx => W.isOneCochain_diffZero hx, W.diffOne_diffZero, fun _ _ h => W.isTwoCochain_diffOne h,
    fun _ _ h => W.cocycle_of_isCob1 h⟩
end Formalism.CoboundaryTransfers
