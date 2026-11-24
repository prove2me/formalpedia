-- Prove2me | solution 1 for Formalism.QuantumDeterminants.eabHTransport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:42:41.905148+00:00
-- url     : https://prove2.me/submissions/43ce287c-6dff-4761-9046-e6bbeeaccae0

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Theorems.Thm_Formalism_QuantumDeterminants_conjugated_generator_transport


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
theorem _root_.solution : EabHTransport := conjugated_generator_transport
end Formalism.QuantumDeterminants
