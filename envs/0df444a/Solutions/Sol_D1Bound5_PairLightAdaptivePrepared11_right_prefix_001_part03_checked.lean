-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared11.right_prefix_001_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:15:30.497914+00:00
-- url     : https://prove2.me/submissions/f28fef37-21b2-4956-b0a9-1be8be519ae3

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 270 through 358, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 89
      (rightCached001.drop 132) (rightRows001.drop 132) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared11
end
