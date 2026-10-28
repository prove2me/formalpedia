-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_002_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:40:26.233282+00:00
-- url     : https://prove2.me/submissions/2f54cd35-1741-498b-9e62-960e0ba14ef1

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 113 through 115; all later vertices retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached002.drop 0) (rightRows002.drop 0) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
