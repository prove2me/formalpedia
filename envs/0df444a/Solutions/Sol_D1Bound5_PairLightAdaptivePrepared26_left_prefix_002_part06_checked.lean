-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:47:19.55699+00:00
-- url     : https://prove2.me/submissions/8aecf563-d4b5-48e4-ab5f-a652fcd2260d

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 131 through 133; all later vertices retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached002.drop 18) (leftRows002.drop 18) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
