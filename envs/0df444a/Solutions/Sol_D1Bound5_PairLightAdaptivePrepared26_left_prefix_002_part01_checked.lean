-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:06:40.297636+00:00
-- url     : https://prove2.me/submissions/cc505389-4714-4373-8d9d-b212c86081e3

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 116 through 118; all later vertices retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached002.drop 3) (leftRows002.drop 3) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
