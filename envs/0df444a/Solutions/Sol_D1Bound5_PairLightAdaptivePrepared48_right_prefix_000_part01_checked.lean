-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared48.right_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:29:09.117859+00:00
-- url     : https://prove2.me/submissions/25da2ea3-489c-4746-adb1-778d7327342e

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 29 through 60; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 32
      (rightCached000.drop 29) (rightRows000.drop 29) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared48
end
