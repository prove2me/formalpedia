-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared8.chunk16_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:57:09.314816+00:00
-- url     : https://prove2.me/submissions/dcb3f4a0-f64c-4b9c-92ca-191f5d3c15ca

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
      (witnesses.drop 1024) (destinations.drop 1024) = true := by
  decide +kernel

end D1Bound5.PairLightClosurePrepared8
end
