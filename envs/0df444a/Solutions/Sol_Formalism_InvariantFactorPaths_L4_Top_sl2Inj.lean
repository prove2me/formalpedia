-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.Top.sl2Inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:06:37.864171+00:00
-- url     : https://prove2.me/submissions/ebea551c-7d21-44b9-8450-7f24c0968607

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundOfRestrictionOfProj
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResSat
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_sl2_injectivity_holds


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
theorem _root_.solution : Sl2Injective := sl2_injectivity_holds
end Formalism.InvariantFactorPaths.L4.Top
