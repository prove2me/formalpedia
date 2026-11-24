-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.leading_minor_one_eq_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:55:35.144816+00:00
-- url     : https://prove2.me/submissions/0f6469f6-d6d0-47f0-add3-91ba963513f7

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
theorem _root_.solution (h1 : 1 ≤ 2) (h2 : 1 ≤ 2) : lpMinor ℤ (r := 2) (n := 2) 1 h1 h2 = X (0, 0) := by
  unfold lpMinor
  rw [Matrix.det_unique]
  rfl
end Formalism.CohomologicalDescent.LD
