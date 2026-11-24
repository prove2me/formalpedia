-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.roots_descent_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:40:12.965896+00:00
-- url     : https://prove2.me/submissions/3153565c-cc11-45a4-b912-a6810efa85c2

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_q_roots_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_rootsDescent_of_roots_and_fourth_relation
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_fourth_relation_holds

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
theorem _root_.solution : RootsDescent := rootsDescent_of_roots_and_fourth_relation q_roots_holds fourth_relation_holds
end Formalism.CohomologicalDescent.HeightDescentMinors
