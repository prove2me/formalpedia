-- Prove2me | solution 1 for D1Bound5.pellFieldCoverageBlock02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:05:00.358975+00:00
-- url     : https://prove2.me/submissions/f9319e48-eb10-40c8-b615-e30134197c7f

import Init
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Exact coverage of original indices 100 through 149. -/
theorem _root_.solution :
    ∀ k : Fin 50, PellFieldCoverageLightAt (100+k.val) := by
  decide +kernel

end D1Bound5
end
