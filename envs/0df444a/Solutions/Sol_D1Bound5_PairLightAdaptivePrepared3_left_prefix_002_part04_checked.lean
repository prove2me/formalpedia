-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared3.left_prefix_002_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:30:02.738745+00:00
-- url     : https://prove2.me/submissions/d9315781-302a-40b3-b583-97b99cd15fc7

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 407 through 412, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 6
      (PairLightPrepared3.leftCached.drop 407)
      (PairLightPrepared3.leftRows.drop 407) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared3
end
