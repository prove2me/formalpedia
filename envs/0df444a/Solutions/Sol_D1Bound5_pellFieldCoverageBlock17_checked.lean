-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock17_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:01:13.574994+00:00
-- url     : https://prove2.me/submissions/fc1bf58d-c7d4-4779-8fde-8b56e36430c9

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 850 through 899. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (850+k.val) := by
  decide +kernel

end D1Bound5
end
