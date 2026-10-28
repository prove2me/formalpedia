-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock10_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:33:15.740617+00:00
-- url     : https://prove2.me/submissions/b8e517d3-4a3c-4d2b-a620-6f211e5726a5

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 500 through 549. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (500+k.val) := by
  decide +kernel

end D1Bound5
end
