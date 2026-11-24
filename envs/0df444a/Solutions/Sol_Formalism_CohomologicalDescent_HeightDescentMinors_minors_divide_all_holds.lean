-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.minors_divide_all_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:40:14.771047+00:00
-- url     : https://prove2.me/submissions/25dd79b9-a20a-45b5-8167-92a38b49d10c

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_dvd_det_submatrix_of_minorsDvd

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
theorem _root_.solution : MinorsDvdAll := by
  intro R _ m p t x P
  exact ⟨fun h f g => dvd_det_submatrix_of_minorsDvd x P h f g, fun h f g _ _ => h f g⟩
end Formalism.CohomologicalDescent.HeightDescentMinors
