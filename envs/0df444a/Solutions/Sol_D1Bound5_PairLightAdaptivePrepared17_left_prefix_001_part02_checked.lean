-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared17.left_prefix_001_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:53:58.050854+00:00
-- url     : https://prove2.me/submissions/a0456150-7551-46f1-9c10-9d59fdc1326e

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 260 through 359; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 100
      (leftCached001.drop 123) (leftRows001.drop 123) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared17
end
