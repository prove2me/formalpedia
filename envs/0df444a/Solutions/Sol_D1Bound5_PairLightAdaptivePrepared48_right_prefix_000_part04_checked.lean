-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared48.right_prefix_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:15.704643+00:00
-- url     : https://prove2.me/submissions/0111b78a-35bb-40ea-abe9-f0cc03c280a8

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 137 through 137; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 1
      (rightCached000.drop 137) (rightRows000.drop 137) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared48
end
