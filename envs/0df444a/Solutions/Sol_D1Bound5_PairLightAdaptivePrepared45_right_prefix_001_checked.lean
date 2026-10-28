-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared45.right_prefix_001_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:58:52.624378+00:00
-- url     : https://prove2.me/submissions/13598193-eff6-4baf-b3c9-fb9bd34d8124

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData45_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData45_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared45
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 43 through 102; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 5 PairLightPrepared45.sieve 60
      rightCached001 rightRows001 = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared45
end
