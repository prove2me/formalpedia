-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared20.right_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:38:03.6394+00:00
-- url     : https://prove2.me/submissions/5ff895ca-5dc8-4856-acc0-30c079027801

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData20_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData20_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared20
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 222; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared20.sieve 223
      rightCached000 rightRows000 = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared20
end
