-- Prove2me | solution 1 for Formalism.LatticeIndexTer.goodIndex_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:15:50.334815+00:00
-- url     : https://prove2.me/submissions/c8c18e87-47d2-4405-afb7-3b275ddfc5fd

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ChainLength
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPowSmulMem
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndex
import Theorems.Thm_Formalism_LatticeIndexTer_goodIndex_of_latFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Formalism.LatticeIndexTer.subgroupData
namespace Formalism.LatticeIndexTer
theorem _root_.solution (h1 : LatFinite) (_h2 : IdxAdd) : GoodIndex := goodIndex_of_latFinite h1
end Formalism.LatticeIndexTer
