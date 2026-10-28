-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock18_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:14:23.199825+00:00
-- url     : https://prove2.me/submissions/b65c6ba1-ddf1-44fe-b92e-f10fec7531ee

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 900 through 949. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (900+k.val) := by
  decide +kernel

end D1Bound5
end
