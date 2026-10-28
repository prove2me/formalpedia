-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared25.left_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:49:45.553983+00:00
-- url     : https://prove2.me/submissions/8b0851a5-b791-4e9c-8837-4f22978fbf83

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 164 through 209, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 46
      (leftCached001.drop 38) (leftRows001.drop 38) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared25
end
