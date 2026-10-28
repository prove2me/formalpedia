-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared25.right_prefix_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:23:21.864916+00:00
-- url     : https://prove2.me/submissions/ef4b8c7b-ed04-4220-bcb1-317671c03ea6

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 109 through 124, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 16
      (rightCached000.drop 109) (rightRows000.drop 109) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared25
end
