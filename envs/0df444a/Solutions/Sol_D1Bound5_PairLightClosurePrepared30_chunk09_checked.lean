-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared30.chunk09_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:05:57.461361+00:00
-- url     : https://prove2.me/submissions/30d0d764-9442-4bb9-b68b-2dccad0bb892

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
      (witnesses.drop 576) (destinations.drop 576) = true := by
  decide +kernel

end D1Bound5.PairLightClosurePrepared30
end
