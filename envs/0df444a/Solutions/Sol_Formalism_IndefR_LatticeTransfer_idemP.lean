-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.idemP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:18:37.303272+00:00
-- url     : https://prove2.me/submissions/7bf1f491-68f8-4c52-9575-3d3ce8a0e69b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransferOfFacts
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_OpNormAtLeOfPoints
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_ExistsStrictHenselianAbsolutelyClosedLocalRing
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransferHolds
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_charFacts
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_idemP_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
namespace Formalism.IndefR.LatticeTransfer
theorem _root_.solution : IdemP := idemP_of charFacts
end Formalism.IndefR.LatticeTransfer
