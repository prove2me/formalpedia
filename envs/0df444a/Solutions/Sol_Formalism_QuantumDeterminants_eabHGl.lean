-- Prove2me | solution 1 for Formalism.QuantumDeterminants.eabHGl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:00:43.104107+00:00
-- url     : https://prove2.me/submissions/92acbb67-6064-4d1a-ab7b-f233e96907ee

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Theorems.Thm_Formalism_QuantumDeterminants_conjugated_generator_gl_relation


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
theorem _root_.solution : EabHGl := conjugated_generator_gl_relation
end Formalism.QuantumDeterminants
