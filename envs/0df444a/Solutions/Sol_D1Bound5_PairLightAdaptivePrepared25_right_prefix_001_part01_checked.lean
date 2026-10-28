-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared25.right_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:37:06.798979+00:00
-- url     : https://prove2.me/submissions/1ac7d2af-c5c2-4dfe-a114-c02b28e17e3a

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 163 through 208, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 46
      (rightCached001.drop 38) (rightRows001.drop 38) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared25
end
