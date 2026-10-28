-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared15.chunk14_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:51.019416+00:00
-- url     : https://prove2.me/submissions/222c4f6a-9928-4df0-a943-23d52466f136

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15_Definitions

section
namespace D1Bound5.PairLightClosurePrepared15
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Both signs retain the full original global destination vertex list. -/
theorem _root_.solution :
    pairLightIndexedWitnessesPrefixBool 0 2 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 896) (destinations.drop 896) = true := by
  decide +kernel

end D1Bound5.PairLightClosurePrepared15
end
