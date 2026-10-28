-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared5.right_prefix_001_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:29:25.038669+00:00
-- url     : https://prove2.me/submissions/dc980588-ec84-45f1-a60e-e56682e0880f

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

/-- Original heads 202 through 225, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 24
      (PairLightPrepared5.rightCached.drop 202)
      (PairLightPrepared5.rightRows.drop 202) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared5
end
