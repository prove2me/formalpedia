-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gGram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:12:04.22502+00:00
-- url     : https://prove2.me/submissions/3992bb24-04f7-4c13-8357-ad5904535680

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Theorems.Thm_Formalism_QuantumDeterminants_group_gram_holds


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
theorem _root_.solution : GGram := group_gram_holds
end Formalism.QuantumDeterminants
