-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared6.chunk19_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T06:13:52.334126+00:00
-- url     : https://prove2.me/submissions/ac10485e-788a-446a-8097-f3946ae03629

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6_Definitions

section
namespace D1Bound5.PairLightClosurePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Both signs retain the full original global destination vertex list. -/
theorem _root_.solution :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 1216) (destinations.drop 1216) = true := by
  decide +kernel

end D1Bound5.PairLightClosurePrepared6
end
