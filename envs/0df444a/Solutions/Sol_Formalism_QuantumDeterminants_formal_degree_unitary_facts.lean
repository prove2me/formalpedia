-- Prove2me | solution 1 for Formalism.QuantumDeterminants.formal_degree_unitary_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:19:57.365113+00:00
-- url     : https://prove2.me/submissions/dc311528-99eb-4c94-838b-6c529ef4485f

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSLowK
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSRatio
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Theorems.Thm_Formalism_QuantumDeterminants_formalDegreeTwoByTwo_holds


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
theorem _root_.solution : FormalDegreeTwoByTwo := formalDegreeTwoByTwo_holds
end Formalism.QuantumDeterminants
