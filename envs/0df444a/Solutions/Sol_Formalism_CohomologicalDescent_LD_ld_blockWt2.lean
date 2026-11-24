-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_blockWt2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:41.370664+00:00
-- url     : https://prove2.me/submissions/898e50e2-3239-4e9c-b667-700d4754b250

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector

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
theorem _root_.solution (w y : ℕ) : blockWt 1 1 w (fun _ : Fin 1 => y) = wt2 w y := by
  funext a
  fin_cases a <;> rfl
end Formalism.CohomologicalDescent.LD
