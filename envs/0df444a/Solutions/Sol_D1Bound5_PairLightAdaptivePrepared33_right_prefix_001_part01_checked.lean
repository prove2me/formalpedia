-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared33.right_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:38:00.712312+00:00
-- url     : https://prove2.me/submissions/08e65fab-b4c7-4ebe-8974-47e28bf8dcc3

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData33_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 189 through 264; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared33.sieve 76
      (rightCached001.drop 51) (rightRows001.drop 51) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared33
end
