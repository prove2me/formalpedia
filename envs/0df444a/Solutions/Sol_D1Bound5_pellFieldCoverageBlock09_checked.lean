-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock09_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:18:23.234814+00:00
-- url     : https://prove2.me/submissions/87b1469b-9eaf-4ad2-b79f-36cf94d5ece7

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 450 through 499. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (450+k.val) := by
  decide +kernel

end D1Bound5
end
