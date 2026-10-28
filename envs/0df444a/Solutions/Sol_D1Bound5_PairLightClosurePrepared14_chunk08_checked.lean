-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared14.chunk08_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:41:43.935454+00:00
-- url     : https://prove2.me/submissions/e8b9c5d9-1fe5-4cbd-aaf3-a843085fdcae

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14_Definitions

section
namespace D1Bound5.PairLightClosurePrepared14
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Both signs retain the full original global destination vertex list. -/
theorem _root_.solution :
    pairLightIndexedWitnessesPrefixBool 0 2 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 512) (destinations.drop 512) = true := by
  decide +kernel

end D1Bound5.PairLightClosurePrepared14
end
