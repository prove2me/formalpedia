-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.leadj_star_ratCast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:21.681789+00:00
-- url     : https://prove2.me/submissions/1117e7f2-0dda-452d-85c7-854025b95e5d

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowAct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (q : ℚ) : star ((q : ℂ)) = (q : ℂ) := by
  exact map_ratCast (starRingEnd ℂ) q
end Formalism.GradedWeylDivisibility
