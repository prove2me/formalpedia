-- Prove2me | solution 1 for Formalism.QuantumDeterminants.linOps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:50:09.322983+00:00
-- url     : https://prove2.me/submissions/f660b454-60cd-470d-a851-c6b60ef6f09c

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRPres
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_AdjointFunctionalHolds
import Definitions.Def_Formalism_YangianSpanCharacter_StatementT
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Theorems.Thm_Formalism_QuantumDeterminants_linear_operators_holds


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
theorem _root_.solution : LinOps := linear_operators_holds
end Formalism.QuantumDeterminants
