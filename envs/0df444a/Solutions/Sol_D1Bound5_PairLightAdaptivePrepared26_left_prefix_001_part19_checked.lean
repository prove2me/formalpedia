-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_001_part19_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:15:36.168012+00:00
-- url     : https://prove2.me/submissions/4107e0ba-3c6f-488e-a597-6d70a22c11b5

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 111 through 112; all later vertices retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 2
      (leftCached001.drop 57) (leftRows001.drop 57) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
