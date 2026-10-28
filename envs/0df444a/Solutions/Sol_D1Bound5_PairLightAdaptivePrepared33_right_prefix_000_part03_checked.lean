-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared33.right_prefix_000_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:25:25.596696+00:00
-- url     : https://prove2.me/submissions/5a091181-5548-40d2-b7b5-a27c68901ff8

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData33_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 96 through 136; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared33.sieve 41
      (rightCached000.drop 96) (rightRows000.drop 96) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared33
end
