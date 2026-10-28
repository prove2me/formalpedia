-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_004_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:39:41.389329+00:00
-- url     : https://prove2.me/submissions/c7b9ef18-81da-4723-a455-ae484e29e8ea

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 275 through 286; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached004.drop 24) (rightRows004.drop 24) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
