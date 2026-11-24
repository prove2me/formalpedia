-- Prove2me | solution 1 for Formalism.QuantumDeterminants.bigCellMinors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:39:47.559399+00:00
-- url     : https://prove2.me/submissions/5e706730-6187-41f5-ab8c-1b1b5ed8d82b

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnipotentEquivHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Theorems.Thm_Formalism_QuantumDeterminants_big_cell_minors_holds


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
theorem _root_.solution : BigCellMinors := big_cell_minors_holds
end Formalism.QuantumDeterminants
