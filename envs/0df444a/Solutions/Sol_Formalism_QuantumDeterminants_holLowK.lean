-- Prove2me | solution 1 for Formalism.QuantumDeterminants.holLowK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:20:26.913225+00:00
-- url     : https://prove2.me/submissions/94a02373-0a80-456c-a804-d8da9eec288e

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSLowK
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSRatio
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Theorems.Thm_Formalism_QuantumDeterminants_holomorphic_low_k_holds


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
theorem _root_.solution : HolLowK := holomorphic_low_k_holds
end Formalism.QuantumDeterminants
