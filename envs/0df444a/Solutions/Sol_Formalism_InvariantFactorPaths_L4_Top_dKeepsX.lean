-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.Top.dKeepsX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:05:38.122242+00:00
-- url     : https://prove2.me/submissions/a2330b32-8bd6-45bf-8453-ff71cac5e672

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundOfRestrictionOfProj
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResSat
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_derivative_keeps_space_holds


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
theorem _root_.solution : DKeepsX := derivative_keeps_space_holds
end Formalism.InvariantFactorPaths.L4.Top
