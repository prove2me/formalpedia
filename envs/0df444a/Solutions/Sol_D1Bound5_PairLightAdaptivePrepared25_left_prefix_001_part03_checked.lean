-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared25.left_prefix_001_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:35:32.427725+00:00
-- url     : https://prove2.me/submissions/d3da5aa5-674f-44a9-8d2a-a2130469b596

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 275 through 379, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 105
      (leftCached001.drop 149) (leftRows001.drop 149) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared25
end
