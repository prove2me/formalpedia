-- Prove2me | solution 1 for D1Bound5.PairLightPrepared47.right_independent_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:38:45.527332+00:00
-- url     : https://prove2.me/submissions/d496eb8c-c27a-43e6-b5d2-568e8f89eb68

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData47_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData47_Definitions_004

section
namespace D1Bound5.PairLightPrepared47
set_option maxRecDepth 100000
set_option maxHeartbeats 0





theorem _root_.solution :
    pairLightSelectedFloorIndependentBool 1 6 sieve rightCached rightRows = true := by
  decide +kernel



end D1Bound5.PairLightPrepared47
end
