-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared3.left_prefix_001_part08_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:29:05.44198+00:00
-- url     : https://prove2.me/submissions/2d0efd95-af1b-4127-af01-968196cd55a2

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

/-- Original heads 304 through 310, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 7
      (PairLightPrepared3.leftCached.drop 304)
      (PairLightPrepared3.leftRows.drop 304) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared3
end
