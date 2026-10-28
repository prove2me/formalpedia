-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared8.chunk19_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:15:29.49699+00:00
-- url     : https://prove2.me/submissions/403734dd-0a71-4916-8fa2-f5515b8824d3

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8_Definitions

section
namespace D1Bound5.PairLightClosurePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Both signs retain the full original global destination vertex list. -/
theorem _root_.solution :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 1216) (destinations.drop 1216) = true := by
  decide +kernel

end D1Bound5.PairLightClosurePrepared8
end
