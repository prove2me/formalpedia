-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared17.left_prefix_000_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:14:24.894896+00:00
-- url     : https://prove2.me/submissions/9b2c5766-55d4-483f-b5a8-0ce5495a67eb

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 94 through 133; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 40
      (leftCached000.drop 94) (leftRows000.drop 94) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared17
end
