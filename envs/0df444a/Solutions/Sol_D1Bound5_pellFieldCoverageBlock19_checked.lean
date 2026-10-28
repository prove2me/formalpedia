-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock19_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:53:56.058996+00:00
-- url     : https://prove2.me/submissions/46678b80-0104-43a1-97ca-1542d2f86df7

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 950 through 999. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (950+k.val) := by
  decide +kernel

end D1Bound5
end
