-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.property_W_of_estimates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:27:44.654592+00:00
-- url     : https://prove2.me/submissions/abbc942f-b9c2-46d6-b8f5-913b6a9f24f5

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_SquareSetMemExceptionalUnion
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateThird
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_PropertyWOfEstimates
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_local_estimate_second
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_local_estimate_third
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_propW_of_localEstimates


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : PropW := propW_of_localEstimates local_estimate_second local_estimate_third
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
