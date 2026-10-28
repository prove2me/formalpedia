-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared44.right_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:06:19.841226+00:00
-- url     : https://prove2.me/submissions/8fb3bcbc-b86c-449f-9206-b403c664cb06

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData44_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData44_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared44
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 219; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 4 PairLightPrepared44.sieve 220
      rightCached000 rightRows000 = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared44
end
