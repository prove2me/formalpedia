-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.depthLastIff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:16:27.612493+00:00
-- url     : https://prove2.me/submissions/4489876f-d40a-43c0-8e73-2ad84ed373ec

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Theorems.Thm_Formalism_CohomologicalDescent_LD_depth_two_block_eq_sum_diff
import Theorems.Thm_Formalism_CohomologicalDescent_LD_sum_block_weight_last

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
theorem _root_.solution : DepthLastIff := by
  intro p q w i lam2 μ hsum
  rw [depth_two_block_eq_sum_diff, sum_block_weight_last, Fin.sum_univ_add] at *
  unfold IsDepthLast
  generalize p * w = pw at *
  omega
end Formalism.CohomologicalDescent.LD
