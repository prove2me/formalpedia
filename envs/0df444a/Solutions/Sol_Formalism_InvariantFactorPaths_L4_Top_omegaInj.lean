-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.Top.omegaInj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:06:22.506863+00:00
-- url     : https://prove2.me/submissions/e00e0f44-1a18-437a-b0e7-260f4854c501

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundOfRestrictionOfProj
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResSat
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_omega_injective_holds


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
theorem _root_.solution : OmegaInj := omega_injective_holds
end Formalism.InvariantFactorPaths.L4.Top
