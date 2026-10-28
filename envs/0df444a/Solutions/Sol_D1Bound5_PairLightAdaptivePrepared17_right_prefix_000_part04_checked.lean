-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared17.right_prefix_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:41:57.798154+00:00
-- url     : https://prove2.me/submissions/607ddbea-43de-4bef-a896-9a8903d2e0ef

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 137 through 137; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 1
      (rightCached000.drop 137) (rightRows000.drop 137) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared17
end
