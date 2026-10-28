-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared43.left_prefix_001_part08_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:09:55.681978+00:00
-- url     : https://prove2.me/submissions/bbd0b181-5309-45ff-904f-bb713bb7ee5a

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

/-- Original heads 187 through 198, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 12
      (PairLightPrepared43.leftCached.drop 187)
      (PairLightPrepared43.leftRows.drop 187) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared43
end
