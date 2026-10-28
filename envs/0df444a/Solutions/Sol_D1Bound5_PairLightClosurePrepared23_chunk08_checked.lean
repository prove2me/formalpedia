-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared23.chunk08_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:23:29.010694+00:00
-- url     : https://prove2.me/submissions/1d1685a4-da33-4929-8441-7a9e43d945a1

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23_Definitions

section
namespace D1Bound5.PairLightClosurePrepared23
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Both signs retain the full original global destination vertex list. -/
theorem _root_.solution :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 512) (destinations.drop 512) = true := by
  decide +kernel

end D1Bound5.PairLightClosurePrepared23
end
