-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.cokernelLengthBound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:08:25.884899+00:00
-- url     : https://prove2.me/submissions/6a94358f-7788-4b93-8eaa-ed142e93d095

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Definitions.Def_Formalism_FrobeniusContraction_FrobeniusContractionProofs_LenBound
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_GammaStableOfGammaQUnitHolds
import Theorems.Thm_Formalism_WachCohomologyFacts_quotientLengthBound_holds


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
theorem _root_.solution : ColBound := by
  intro O A _ _ _ B M D D' _ _ _ _ _ _ _ _ W W' F g e hfin hlift
  obtain ⟨s, hs, hspan⟩ := hfin
  show Module.length O (↥W'.Zf ⧸ F.ImF.comap W'.Zf.subtype) ≤ _
  first
    | exact Formalism.WachCohomologyFacts.quotientLengthBound_holds O (D' × D') B.p g e W'.Zf W'.B1 F.ImF s hs hspan le_sup_right hlift
    | exact Formalism.WachCohomologyFacts.PLenBound.quotientLengthBound_holds O (D' × D') B.p g e W'.Zf W'.B1 F.ImF s hs hspan le_sup_right hlift
    | exact _root_.quotientLengthBound_holds O (D' × D') B.p g e W'.Zf W'.B1 F.ImF s hs hspan le_sup_right hlift
end Formalism.CoboundaryTransfers
