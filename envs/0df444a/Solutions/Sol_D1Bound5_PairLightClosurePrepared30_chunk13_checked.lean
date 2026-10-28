-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared30.chunk13_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:16:12.235993+00:00
-- url     : https://prove2.me/submissions/36766fc2-2150-48eb-8a51-16038ae2652d

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30_Definitions

section
namespace D1Bound5.PairLightClosurePrepared30
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Both signs retain the full original global destination vertex list. -/
theorem _root_.solution :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 832) (destinations.drop 832) = true := by
  decide +kernel

end D1Bound5.PairLightClosurePrepared30
end
