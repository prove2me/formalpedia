-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock24_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:00:42.395481+00:00
-- url     : https://prove2.me/submissions/c0be1fa4-b96a-45b1-8044-8cd4faeef757

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 1200 through 1249. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (1200+k.val) := by
  decide +kernel

end D1Bound5
end
