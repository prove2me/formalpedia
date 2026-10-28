-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared33.left_prefix_000_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:43.351868+00:00
-- url     : https://prove2.me/submissions/eceed0dd-d737-42d9-bc90-b63a6d6ab420

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData33_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 94 through 133; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared33.sieve 40
      (leftCached000.drop 94) (leftRows000.drop 94) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared33
end
