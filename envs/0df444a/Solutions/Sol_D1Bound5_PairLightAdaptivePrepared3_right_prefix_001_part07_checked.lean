-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared3.right_prefix_001_part07_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:33:30.666988+00:00
-- url     : https://prove2.me/submissions/9bab9d0f-5a80-4cff-9ac4-a6a0c780cbf9

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 279 through 302, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 24
      (PairLightPrepared3.rightCached.drop 279)
      (PairLightPrepared3.rightRows.drop 279) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared3
end
