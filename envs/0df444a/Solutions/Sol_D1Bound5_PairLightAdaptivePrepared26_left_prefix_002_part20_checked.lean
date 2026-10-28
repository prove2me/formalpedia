-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part20_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:19:08.326275+00:00
-- url     : https://prove2.me/submissions/4e61d19f-7297-4cbd-82f5-2d54d56f17b6

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 173 through 175; all later vertices retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached002.drop 60) (leftRows002.drop 60) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
