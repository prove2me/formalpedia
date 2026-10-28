-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock08_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:29:25.849138+00:00
-- url     : https://prove2.me/submissions/71febecd-609e-4e0e-ac16-afff0c585a34

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 400 through 449. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (400+k.val) := by
  decide +kernel

end D1Bound5
end
