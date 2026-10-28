-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared30.chunk15_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:49:26.463435+00:00
-- url     : https://prove2.me/submissions/7f1c2dda-b8d6-49cd-9eac-eca87d39fd85

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
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 3
      (witnesses.drop 960) (destinations.drop 960) = true := by
  decide +kernel

end D1Bound5.PairLightClosurePrepared30
end
