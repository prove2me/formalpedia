-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock13_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:46:23.801475+00:00
-- url     : https://prove2.me/submissions/307e0ffa-f1b2-4ffb-94a3-0b3246e3942b

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 650 through 699. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (650+k.val) := by
  decide +kernel

end D1Bound5
end
