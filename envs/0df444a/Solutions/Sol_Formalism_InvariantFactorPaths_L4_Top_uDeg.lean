-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.Top.uDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:21:22.561691+00:00
-- url     : https://prove2.me/submissions/e0f3808d-9e43-47e6-9bd1-4020129ddf03

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundOfRestrictionOfProj
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResSat
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_raising_degree_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4 Formalism.InvariantFactorPaths.L4.Top
open Formalism.InvariantFactorPaths.L4
namespace Formalism.InvariantFactorPaths.L4.Top
theorem _root_.solution : UDeg := raising_degree_holds
end Formalism.InvariantFactorPaths.L4.Top
