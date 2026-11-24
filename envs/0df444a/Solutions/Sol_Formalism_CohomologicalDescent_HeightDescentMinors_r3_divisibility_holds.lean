-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.r3_divisibility_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:40:08.484959+00:00
-- url     : https://prove2.me/submissions/f3650c69-c8a8-4d61-98eb-d5cb71efd9ee

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_q_roots_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_r3_divisibility_of_unit_roots
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
theorem _root_.solution : RootOfUnityRemainder := r3_divisibility_of_unit_roots r3_unit_holds q_roots_holds
end Formalism.CohomologicalDescent.HeightDescentMinors
