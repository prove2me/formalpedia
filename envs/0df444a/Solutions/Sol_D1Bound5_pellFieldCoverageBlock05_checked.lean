-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:15:45.026312+00:00
-- url     : https://prove2.me/submissions/f89d6439-56ae-459b-a764-b7f92935d861

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 250 through 299. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (250+k.val) := by
  decide +kernel

end D1Bound5
end
