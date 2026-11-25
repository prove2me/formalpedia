-- Prove2me | solution 1 for Formalism.QuantumDeterminants.bigCellMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:30:24.092851+00:00
-- url     : https://prove2.me/submissions/8191e4c8-2a1e-40d7-9d1d-52332317f1e2

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnipotentEquivHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Theorems.Thm_Formalism_QuantumDeterminants_big_cell_mem_holds


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
theorem _root_.solution : BigCellMem := big_cell_mem_holds
end Formalism.QuantumDeterminants
