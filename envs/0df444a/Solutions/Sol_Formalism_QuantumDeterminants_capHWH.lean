-- Prove2me | solution 1 for Formalism.QuantumDeterminants.capHWH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:54:09.243059+00:00
-- url     : https://prove2.me/submissions/f1deca56-6dc9-431f-b059-1f4932e19bf7

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Theorems.Thm_Formalism_QuantumDeterminants_capelli_highest_weight_conjugated


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
theorem _root_.solution : CapHWH := capelli_highest_weight_conjugated
end Formalism.QuantumDeterminants
