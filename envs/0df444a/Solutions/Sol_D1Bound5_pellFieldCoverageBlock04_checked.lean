-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:16:59.675602+00:00
-- url     : https://prove2.me/submissions/3f9e7ac9-cea6-4f63-8e0c-12cffa2f8192

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 200 through 249. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (200+k.val) := by
  decide +kernel

end D1Bound5
end
