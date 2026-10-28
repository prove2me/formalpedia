-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock11_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:31:43.704109+00:00
-- url     : https://prove2.me/submissions/ff9bb707-d0e6-4c41-a229-07cf9e75794d

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 550 through 599. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (550+k.val) := by
  decide +kernel

end D1Bound5
end
