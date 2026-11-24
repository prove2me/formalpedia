-- Prove2me | solution 1 for Formalism.QuantumDeterminants.capCentralH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:11:40.998806+00:00
-- url     : https://prove2.me/submissions/1aa1e2e3-42ef-4483-a9c5-9032068d00f1

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Theorems.Thm_Formalism_QuantumDeterminants_capelli_central_conjugated


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
theorem _root_.solution : CapCentralH := capelli_central_conjugated
end Formalism.QuantumDeterminants
