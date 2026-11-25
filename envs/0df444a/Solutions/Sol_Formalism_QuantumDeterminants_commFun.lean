-- Prove2me | solution 1 for Formalism.QuantumDeterminants.commFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:39:34.230497+00:00
-- url     : https://prove2.me/submissions/fbfd4099-08fd-4584-bbf9-ead096875745

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRPres
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_AdjointFunctionalHolds
import Definitions.Def_Formalism_YangianSpanCharacter_StatementT
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Theorems.Thm_Formalism_QuantumDeterminants_commuting_functional_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution : CommFun := commuting_functional_holds
end Formalism.QuantumDeterminants
