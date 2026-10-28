-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared5.right_prefix_000_part07_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:16:22.461442+00:00
-- url     : https://prove2.me/submissions/488d2a6c-3ac2-403c-b9d9-190c11a728f9

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 84 through 95, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 12
      (PairLightPrepared5.rightCached.drop 84)
      (PairLightPrepared5.rightRows.drop 84) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared5
end
