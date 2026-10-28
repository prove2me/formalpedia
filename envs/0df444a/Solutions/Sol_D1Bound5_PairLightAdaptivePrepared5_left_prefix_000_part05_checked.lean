-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared5.left_prefix_000_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:43:40.965985+00:00
-- url     : https://prove2.me/submissions/6dcca1c3-fcf7-4d2f-b20e-cf7685908b2d

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 60 through 71, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 12
      (PairLightPrepared5.leftCached.drop 60)
      (PairLightPrepared5.leftRows.drop 60) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared5
end
