-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock21_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:16:25.015695+00:00
-- url     : https://prove2.me/submissions/1e3e2449-36c5-4807-bec2-7c1b2c9ad02b

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 1050 through 1099. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (1050+k.val) := by
  decide +kernel

end D1Bound5
end
