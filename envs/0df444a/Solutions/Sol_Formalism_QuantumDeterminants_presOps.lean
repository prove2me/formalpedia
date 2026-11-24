-- Prove2me | solution 1 for Formalism.QuantumDeterminants.presOps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:50:09.995601+00:00
-- url     : https://prove2.me/submissions/e8853057-1472-4e20-b4b6-f365b24d3560

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRPres
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_AdjointFunctionalHolds
import Definitions.Def_Formalism_YangianSpanCharacter_StatementT
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Theorems.Thm_Formalism_QuantumDeterminants_preserved_operators_holds


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
theorem _root_.solution : PresOps := preserved_operators_holds
end Formalism.QuantumDeterminants
