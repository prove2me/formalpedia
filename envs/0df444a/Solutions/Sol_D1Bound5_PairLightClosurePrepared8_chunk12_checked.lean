-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared8.chunk12_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:21:49.429978+00:00
-- url     : https://prove2.me/submissions/723bdfee-a394-4d13-8b21-af008bd38a08

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
      (witnesses.drop 768) (destinations.drop 768) = true := by
  decide +kernel

end D1Bound5.PairLightClosurePrepared8
end
