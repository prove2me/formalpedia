-- Prove2me | solution 1 for Formalism.QuantumDeterminants.lowKInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:22:03.132927+00:00
-- url     : https://prove2.me/submissions/974db4c2-4048-4147-a582-20fb3a7fb2e8

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSLowK
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSRatio
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Theorems.Thm_Formalism_QuantumDeterminants_low_k_integrable_holds


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
theorem _root_.solution : LowKInt := low_k_integrable_holds
end Formalism.QuantumDeterminants
