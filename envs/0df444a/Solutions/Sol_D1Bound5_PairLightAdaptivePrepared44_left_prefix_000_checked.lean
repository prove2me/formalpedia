-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared44.left_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:12:22.957906+00:00
-- url     : https://prove2.me/submissions/2015c991-349c-4956-ba4c-d3e8b8bb556c

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
      leftCached000 leftRows000 = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared44
end
