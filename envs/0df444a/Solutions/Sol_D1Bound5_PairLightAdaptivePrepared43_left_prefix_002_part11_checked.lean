-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared43.left_prefix_002_part11_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:12:16.789247+00:00
-- url     : https://prove2.me/submissions/bc3f7827-143e-4ce4-a2c1-30d1be285002

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 476 through 481, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 6
      (PairLightPrepared43.leftCached.drop 476)
      (PairLightPrepared43.leftRows.drop 476) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared43
end
