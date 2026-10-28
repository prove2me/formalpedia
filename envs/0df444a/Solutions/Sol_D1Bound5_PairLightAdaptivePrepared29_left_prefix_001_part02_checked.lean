-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared29.left_prefix_001_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:35:01.019475+00:00
-- url     : https://prove2.me/submissions/8acc5ca2-b318-4146-bb21-aa9cbc997ca5

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 210 through 274, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 65
      (leftCached001.drop 84) (leftRows001.drop 84) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared29
end
