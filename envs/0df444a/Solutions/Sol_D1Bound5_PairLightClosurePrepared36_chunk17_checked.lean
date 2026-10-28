-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared36.chunk17_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:25:44.89698+00:00
-- url     : https://prove2.me/submissions/720a7702-d9d7-4af9-8b5b-e02703e3e32e

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36_Definitions

section
namespace D1Bound5.PairLightClosurePrepared36
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Both signs retain the full original global destination vertex list. -/
theorem _root_.solution :
    pairLightIndexedWitnessesPrefixBool 1 2 a b anchorRoot (10^1100) vertices 35
      (witnesses.drop 1088) (destinations.drop 1088) = true := by
  decide +kernel

end D1Bound5.PairLightClosurePrepared36
end
