-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:29:31.524975+00:00
-- url     : https://prove2.me/submissions/1b43bc95-e8ea-445b-b007-624b2cbf05a0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransferOfFacts
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_OpNormAtLeOfPoints
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_ExistsStrictHenselianAbsolutelyClosedLocalRing
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransferHolds
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_idemP
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_charFacts
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_core_of
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_keyZero
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_schur


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
theorem _root_.solution : Core := core_of charFacts keyZero schur idemP
end Formalism.IndefR.LatticeTransfer
