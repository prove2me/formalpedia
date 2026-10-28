-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared25.right_prefix_001_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:45:42.911663+00:00
-- url     : https://prove2.me/submissions/cc8e966c-71a8-4670-8bb9-63ff0f5573c2

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 125 through 162, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 38
      (rightCached001.drop 0) (rightRows001.drop 0) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared25
end
