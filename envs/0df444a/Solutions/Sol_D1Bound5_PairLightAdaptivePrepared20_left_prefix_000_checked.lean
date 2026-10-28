-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared20.left_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:47:16.928259+00:00
-- url     : https://prove2.me/submissions/1be80a42-48ec-4823-b2f5-b772e90ab449

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData20_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared20
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 222; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared20.sieve 223
      leftCached000 leftRows000 = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared20
end
