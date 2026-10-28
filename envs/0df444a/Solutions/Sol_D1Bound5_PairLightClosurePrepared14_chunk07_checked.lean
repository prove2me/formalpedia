-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared14.chunk07_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:12:28.680496+00:00
-- url     : https://prove2.me/submissions/53e801dc-8fb1-4aba-9d09-bd71f4572761

import Init
import Definitions.Def_D1Bound5_PairLightClosure_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14Destinations_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14Vertices_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14_Definitions

section
namespace D1Bound5.PairLightClosurePrepared14
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Both signs retain the full original global destination vertex list. -/
theorem _root_.solution :
    pairLightIndexedWitnessesPrefixBool 0 2 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 448) (destinations.drop 448) = true := by
  decide +kernel

end D1Bound5.PairLightClosurePrepared14
end
