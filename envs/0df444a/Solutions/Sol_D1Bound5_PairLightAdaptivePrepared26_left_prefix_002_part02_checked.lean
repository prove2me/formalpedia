-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:16:31.69019+00:00
-- url     : https://prove2.me/submissions/dd2fed37-6764-430a-8bec-a2824fee23ef

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 119 through 121; all later vertices retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached002.drop 6) (leftRows002.drop 6) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
