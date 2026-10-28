-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_007_part12_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:43:40.621878+00:00
-- url     : https://prove2.me/submissions/ad6730c3-a152-45e4-a313-d6c8b8307fe0

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 760 through 760; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 1
      (leftCached007.drop 144) (leftRows007.drop 144) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
