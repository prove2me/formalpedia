-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared21.chunk16_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:27:21.231261+00:00
-- url     : https://prove2.me/submissions/eb9be732-8d65-4f79-b26d-546e4d03a373

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21_Definitions

section
namespace D1Bound5.PairLightClosurePrepared21
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Both signs retain the full original global destination vertex list. -/
theorem _root_.solution :
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 25
      (witnesses.drop 1024) (destinations.drop 1024) = true := by
  decide +kernel

end D1Bound5.PairLightClosurePrepared21
end
