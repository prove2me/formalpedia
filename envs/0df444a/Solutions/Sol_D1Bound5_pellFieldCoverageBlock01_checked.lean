-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:20:08.945372+00:00
-- url     : https://prove2.me/submissions/fd6e3f18-4a6e-4a83-b8a0-f4626f72de9d

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 50 through 99. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (50+k.val) := by
  decide +kernel

end D1Bound5
end
