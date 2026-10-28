-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock12_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:34:05.892315+00:00
-- url     : https://prove2.me/submissions/01f05b4a-de31-465e-8f0b-3c868ecba3b5

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 600 through 649. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (600+k.val) := by
  decide +kernel

end D1Bound5
end
