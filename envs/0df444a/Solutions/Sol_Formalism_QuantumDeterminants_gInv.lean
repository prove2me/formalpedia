-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:51:22.336799+00:00
-- url     : https://prove2.me/submissions/bad39cf8-8675-4c93-bb42-70dc136632d3

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Theorems.Thm_Formalism_QuantumDeterminants_group_inverse_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution : GInv := group_inverse_holds
end Formalism.QuantumDeterminants
