-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.dimSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:19:32.51491+00:00
-- url     : https://prove2.me/submissions/37814ea3-4754-4bfe-8a44-ec167afddf80

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransferOfFacts
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_OpNormAtLeOfPoints
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_ExistsStrictHenselianAbsolutelyClosedLocalRing
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransferHolds
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_dimSq_of
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
theorem _root_.solution : DimSq := dimSq_of schur
end Formalism.IndefR.LatticeTransfer
