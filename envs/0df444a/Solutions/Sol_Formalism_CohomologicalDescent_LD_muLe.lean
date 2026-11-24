-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.muLe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:55:40.555532+00:00
-- url     : https://prove2.me/submissions/0c8d78c1-1f34-4d6a-af47-bf8ea93c525b

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_boxes_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : MuLe := by
  intro p w i q lam2 c
  unfold mu
  exact Finset.sup_le fun tau h => ld_boxes_le p w i q lam2 tau h c
end Formalism.CohomologicalDescent.LD
