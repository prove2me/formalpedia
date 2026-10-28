-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared36.chunk08_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:08:10.869896+00:00
-- url     : https://prove2.me/submissions/c7cfc506-abad-4091-a85b-f1530743ced9

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
    pairLightIndexedWitnessesPrefixBool 1 2 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 512) (destinations.drop 512) = true := by
  decide +kernel

end D1Bound5.PairLightClosurePrepared36
end
