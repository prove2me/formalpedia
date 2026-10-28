-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared4.chunk18_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:29:33.57991+00:00
-- url     : https://prove2.me/submissions/d0191bd0-672a-436e-b9f9-46700a35edd6

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
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 43
      (witnesses.drop 1152) (destinations.drop 1152) = true := by
  decide +kernel

end D1Bound5.PairLightClosurePrepared4
end
