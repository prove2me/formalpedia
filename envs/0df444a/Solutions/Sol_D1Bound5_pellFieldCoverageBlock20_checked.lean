-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock20_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:43:51.488833+00:00
-- url     : https://prove2.me/submissions/16b17692-5ade-40fe-a0cf-8014ee74243d

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 1000 through 1049. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (1000+k.val) := by
  decide +kernel

end D1Bound5
end
