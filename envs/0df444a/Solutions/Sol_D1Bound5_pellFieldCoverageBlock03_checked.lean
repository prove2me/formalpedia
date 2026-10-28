-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:40:21.23198+00:00
-- url     : https://prove2.me/submissions/f5ce267c-9299-4860-909d-e9f1352ceafc

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 150 through 199. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (150+k.val) := by
  decide +kernel

end D1Bound5
end
