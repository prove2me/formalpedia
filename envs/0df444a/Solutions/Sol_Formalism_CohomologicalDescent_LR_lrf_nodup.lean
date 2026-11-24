-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrf_nodup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:18.441099+00:00
-- url     : https://prove2.me/submissions/74f61a7e-5dbe-4d53-9f81-486e2c0136cb

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrf_pairwise

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution : ((lrf_L r n).map (·.2.2)).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  exact (lrf_pairwise (r := r) (n := n)).imp fun h => h.1
end Formalism.CohomologicalDescent.LR
