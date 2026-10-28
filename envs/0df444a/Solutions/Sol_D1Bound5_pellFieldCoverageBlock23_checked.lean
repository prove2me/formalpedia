-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock23_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:20:42.654985+00:00
-- url     : https://prove2.me/submissions/85eb33e2-06f9-4925-ae9f-4d95fe53f0a6

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 1150 through 1199. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (1150+k.val) := by
  decide +kernel

end D1Bound5
end
