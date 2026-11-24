-- Prove2me | solution 1 for Formalism.QuantumDeterminants.capLeftH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:39:26.844856+00:00
-- url     : https://prove2.me/submissions/2b782c71-77bd-4289-813d-ccc1ee0ebf25

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Theorems.Thm_Formalism_QuantumDeterminants_capelli_left_conjugated


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
theorem _root_.solution : CapLeftH := capelli_left_conjugated
end Formalism.QuantumDeterminants
