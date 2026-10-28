-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared48.left_prefix_001_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:49:03.915405+00:00
-- url     : https://prove2.me/submissions/a2b0b8f6-023a-48e7-899a-0d2241bb1a1b

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 260 through 359; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 100
      (leftCached001.drop 123) (leftRows001.drop 123) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared48
end
