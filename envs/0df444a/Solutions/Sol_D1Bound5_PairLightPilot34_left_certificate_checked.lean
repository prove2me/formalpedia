-- Prove2me | solution 1 for D1Bound5.PairLightPilot34.left_certificate_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:13:30.371858+00:00
-- url     : https://prove2.me/submissions/124e8f21-db29-443b-8440-8ad6d3112ca2

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData34_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData34_Definitions_002

section
namespace D1Bound5.PairLightPilot34
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Only the isolated arithmetic computation. Connection to the original
class requires the separately checked data equalities and exact bridge. -/
theorem _root_.solution :
    pairLightSelectedFloorIndependentCertificateBool 1 2 sieve
      leftVertices leftCached leftRows = true := by
  decide +kernel

end D1Bound5.PairLightPilot34
end
