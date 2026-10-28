-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared48.right_prefix_000_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:21:39.702174+00:00
-- url     : https://prove2.me/submissions/1f4e015c-e0dc-4c9b-901e-3c2c8606bccb

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 96 through 136; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 41
      (rightCached000.drop 96) (rightRows000.drop 96) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared48
end
