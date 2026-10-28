-- Prove2me | solution 1 for D1Bound5.PairLightRightPilot34.right_certificate_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:28:17.606076+00:00
-- url     : https://prove2.me/submissions/8267f45e-d134-4b36-82f6-49f7fb100b0d

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightRightData34_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightRightData34_Definitions_002

section
namespace D1Bound5.PairLightRightPilot34
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Only the isolated arithmetic computation. Connection to the original
class requires the separately checked data equalities and exact bridge. -/
theorem _root_.solution :
    pairLightSelectedFloorIndependentCertificateBool 1 2 sieve
      rightVertices rightCached rightRows = true := by
  decide +kernel

end D1Bound5.PairLightRightPilot34
end
