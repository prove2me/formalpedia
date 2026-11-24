-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.height_descent_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:39:50.618972+00:00
-- url     : https://prove2.me/submissions/5279b2dc-94de-44ae-98ee-9b8b430dfc87

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_height_descent_of_r3_r2
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r2_basis_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r3_unit_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : HeightDescent := height_descent_of_r3_r2 r3_unit_holds r2_basis_holds
end Formalism.CohomologicalDescent.HeightDescentMinors
