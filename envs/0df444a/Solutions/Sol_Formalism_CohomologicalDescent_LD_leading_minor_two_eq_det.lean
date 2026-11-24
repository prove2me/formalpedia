-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.leading_minor_two_eq_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:44:46.943931+00:00
-- url     : https://prove2.me/submissions/e2cd5280-d8ba-4703-909d-8d8021daa3a3

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
theorem _root_.solution (h1 : 2 ≤ 2) (h2 : 2 ≤ 2) : lpMinor ℤ (r := 2) (n := 2) 2 h1 h2 = ldDet := by
  unfold lpMinor
  rw [Matrix.det_fin_two]
  rfl
end Formalism.CohomologicalDescent.LD
