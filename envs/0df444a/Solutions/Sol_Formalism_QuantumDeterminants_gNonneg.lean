-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gNonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:12:03.66029+00:00
-- url     : https://prove2.me/submissions/b64ad0e4-2d67-44e0-985d-365fa947cefa

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Theorems.Thm_Formalism_QuantumDeterminants_gNonneg_of
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
theorem _root_.solution : GNonneg := gNonneg_of group_gram_holds
end Formalism.QuantumDeterminants
