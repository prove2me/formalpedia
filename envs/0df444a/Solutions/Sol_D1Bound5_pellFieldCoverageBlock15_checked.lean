-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock15_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:37:16.923713+00:00
-- url     : https://prove2.me/submissions/43af79e3-2ce0-45be-abf9-88bacc3c4635

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 750 through 799. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (750+k.val) := by
  decide +kernel

end D1Bound5
end
