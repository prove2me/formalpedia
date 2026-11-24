-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.rank_two_vector_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:54:05.968662+00:00
-- url     : https://prove2.me/submissions/8b412c76-b185-4add-a6ce-08d4a0b1600a

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_rank_two_vector_def
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_det_ne

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
theorem _root_.solution (w y i : ℕ) : vec2 w y i ≠ 0 := by
  rw [rank_two_vector_def]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (X_ne_zero _)) (pow_ne_zero _ (X_ne_zero _)))
    (pow_ne_zero _ ld_det_ne)
end Formalism.CohomologicalDescent.LD
