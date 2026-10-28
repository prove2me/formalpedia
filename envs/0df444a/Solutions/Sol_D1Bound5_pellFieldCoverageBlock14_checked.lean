-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock14_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:32:00.59746+00:00
-- url     : https://prove2.me/submissions/b13e1061-2e06-4cd4-b272-1a4aa3cbfdd0

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 700 through 749. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (700+k.val) := by
  decide +kernel

end D1Bound5
end
