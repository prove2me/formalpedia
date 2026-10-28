-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared48.right_prefix_000_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:49:33.291726+00:00
-- url     : https://prove2.me/submissions/e0151ea9-991a-46fe-8a45-0122f66e6ebd

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 61 through 95; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 35
      (rightCached000.drop 61) (rightRows000.drop 61) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared48
end
