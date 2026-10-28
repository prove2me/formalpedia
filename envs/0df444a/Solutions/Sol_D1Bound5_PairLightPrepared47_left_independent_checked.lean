-- Prove2me | solution 1 for D1Bound5.PairLightPrepared47.left_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:48:14.893288+00:00
-- url     : https://prove2.me/submissions/8f702edf-7287-4d4d-a0b2-a90d0fdea472

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData47_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData47_Definitions_002

section
namespace D1Bound5.PairLightPrepared47
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 6 sieve leftCached leftRows = true := by
  decide +kernel



end D1Bound5.PairLightPrepared47
end
