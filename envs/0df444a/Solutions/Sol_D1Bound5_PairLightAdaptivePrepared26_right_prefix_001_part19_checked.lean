-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_001_part19_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:17:02.360406+00:00
-- url     : https://prove2.me/submissions/85f57e31-f098-413b-bd45-dc331c52df15

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 111 through 112; all later vertices retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 2
      (rightCached001.drop 57) (rightRows001.drop 57) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
