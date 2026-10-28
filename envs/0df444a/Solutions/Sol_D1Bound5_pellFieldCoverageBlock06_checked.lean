-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:05:48.937965+00:00
-- url     : https://prove2.me/submissions/3b5656a8-5fc9-43e1-8a9b-c0ebf6360105

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 300 through 349. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (300+k.val) := by
  decide +kernel

end D1Bound5
end
