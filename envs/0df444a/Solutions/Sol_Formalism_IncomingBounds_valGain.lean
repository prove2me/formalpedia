-- Prove2me | solution 1 for Formalism.IncomingBounds.valGain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:07:11.610017+00:00
-- url     : https://prove2.me/submissions/981bd906-9548-4622-9eb7-e161b8cdfcf4

import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaF
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaFd
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_BaseTermLeTopTerm
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_AltChooseSumEqZero
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_IndexLastReductionHolds
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Series
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Formalism_IncomingBounds_WeightIdentities
import Theorems.Thm_Formalism_IncomingBounds_padicValuationGain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : ValGain := padicValuationGain
end Formalism.IncomingBounds
