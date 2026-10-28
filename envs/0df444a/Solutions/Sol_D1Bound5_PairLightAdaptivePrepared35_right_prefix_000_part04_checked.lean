-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared35.right_prefix_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:09:54.878271+00:00
-- url     : https://prove2.me/submissions/d54fd050-df67-4d00-a269-20c033a3bd21

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 131 through 131; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 1
      (rightCached000.drop 131) (rightRows000.drop 131) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared35
end
