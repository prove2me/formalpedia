-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock16_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:24:04.991761+00:00
-- url     : https://prove2.me/submissions/e5d55428-4128-42df-8a9a-f65f1f426154

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 800 through 849. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (800+k.val) := by
  decide +kernel

end D1Bound5
end
