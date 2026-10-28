-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared4.chunk07_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:43:49.995513+00:00
-- url     : https://prove2.me/submissions/55cd39e6-1178-4a3d-9229-e5c36bf0eb9b

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4_Definitions

section
namespace D1Bound5.PairLightClosurePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Both signs retain the full original global destination vertex list. -/
theorem _root_.solution :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 448) (destinations.drop 448) = true := by
  decide +kernel

end D1Bound5.PairLightClosurePrepared4
end
