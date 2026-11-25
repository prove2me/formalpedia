-- Prove2me | solution 1 for Formalism.QuantumDeterminants.holHC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:20:19.006929+00:00
-- url     : https://prove2.me/submissions/025544aa-fe0f-41e8-bc31-72b08233990f

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSLowK
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSRatio
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Theorems.Thm_Formalism_QuantumDeterminants_holomorphic_harish_chandra_holds


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
theorem _root_.solution : HolHC := holomorphic_harish_chandra_holds
end Formalism.QuantumDeterminants
