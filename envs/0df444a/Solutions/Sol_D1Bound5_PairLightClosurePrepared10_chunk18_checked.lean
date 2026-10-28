-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared10.chunk18_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:38:44.79425+00:00
-- url     : https://prove2.me/submissions/b5c0dcce-70c0-42e1-9bcb-5a6366ee29bb

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData10_Definitions

section
namespace D1Bound5.PairLightClosurePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Both signs retain the full original global destination vertex list. -/
theorem _root_.solution :
    pairLightIndexedWitnessesPrefixBool 0 1 a b anchorRoot (10^1100) vertices 42
      (witnesses.drop 1152) (destinations.drop 1152) = true := by
  decide +kernel

end D1Bound5.PairLightClosurePrepared10
end
