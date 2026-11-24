-- Prove2me | solution 1 for Formalism.QuantumDeterminants.bigCellZhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:33:26.735834+00:00
-- url     : https://prove2.me/submissions/4941b7be-2f02-4172-8654-2ee98c9263cf

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnipotentEquivHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Theorems.Thm_Formalism_QuantumDeterminants_big_cell_coordinate_holds


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
theorem _root_.solution : BigCellZhat := big_cell_coordinate_holds
end Formalism.QuantumDeterminants
