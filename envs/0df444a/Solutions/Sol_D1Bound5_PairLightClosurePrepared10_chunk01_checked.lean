-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared10.chunk01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:58:39.607979+00:00
-- url     : https://prove2.me/submissions/ceec26ce-7de9-49d1-b5e2-9e165477e4f4

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10_Definitions

section
namespace D1Bound5.PairLightClosurePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Both signs retain the full original global destination vertex list. -/
theorem _root_.solution :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 64) (destinations.drop 64) = true := by
  decide +kernel

end D1Bound5.PairLightClosurePrepared10
end
