-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.standardMonomialSpanOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:00.739956+00:00
-- url     : https://prove2.me/submissions/102b0133-c0d1-4e44-90d4-dd110a69b3ce

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_StandardMonomialSpanOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : StandardMonomialSpanOf := by
  intro h r n ν _
  exact h ℤ r n ν
end Formalism.GradedWeylDivisibility
