-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock07_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:40:02.239997+00:00
-- url     : https://prove2.me/submissions/32cec698-7363-4db1-b59c-8763bddb2adf

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 350 through 399. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (350+k.val) := by
  decide +kernel

end D1Bound5
end
