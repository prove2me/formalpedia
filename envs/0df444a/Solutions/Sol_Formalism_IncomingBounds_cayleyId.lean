-- Prove2me | solution 1 for Formalism.IncomingBounds.cayleyId
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:03:48.668346+00:00
-- url     : https://prove2.me/submissions/b8d8c3f3-0e34-4505-bff0-a65eb14e81b9

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
import Theorems.Thm_Formalism_IncomingBounds_cayleyIdentity


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
theorem _root_.solution : CayleyId := cayleyIdentity
end Formalism.IncomingBounds
