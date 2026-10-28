-- Prove2me | solution 1 for D1Bound5.PairLightClosurePrepared21.chunk11_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:35:58.570995+00:00
-- url     : https://prove2.me/submissions/76b1e8e5-a73a-425e-ac18-20e2da1bc684

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
    pairLightIndexedWitnessesPrefixBool 1 1 a b anchorRoot (10^1100) vertices 64
      (witnesses.drop 704) (destinations.drop 704) = true := by
  decide +kernel

end D1Bound5.PairLightClosurePrepared21
end
