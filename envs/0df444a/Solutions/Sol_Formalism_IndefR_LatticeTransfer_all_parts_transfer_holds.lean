-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.all_parts_transfer_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:12:59.312805+00:00
-- url     : https://prove2.me/submissions/b308c0ad-2ea4-4758-937c-032e06909a96

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransferOfFacts
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_OpNormAtLeOfPoints
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_ExistsStrictHenselianAbsolutelyClosedLocalRing
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransferHolds
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_dimSq
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_idemP
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_core
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_all_parts_transfer_of_facts
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_idemE
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_metric


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
theorem _root_.solution : AllPartsTransfer := all_parts_transfer_of_facts idemE idemP core dimSq metric
end Formalism.IndefR.LatticeTransfer
