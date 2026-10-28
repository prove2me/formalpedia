-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_001_part07_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:25:58.609676+00:00
-- url     : https://prove2.me/submissions/26fd2e14-3dfe-430a-9614-4c1f13cf831e

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 75 through 77; all later vertices retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached001.drop 21) (rightRows001.drop 21) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
