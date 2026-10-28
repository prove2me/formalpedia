-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared5.right_prefix_001_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:10.36636+00:00
-- url     : https://prove2.me/submissions/4d9fd70e-5d96-4ba7-9c09-c5297648e125

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

/-- Original heads 154 through 177, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 24
      (PairLightPrepared5.rightCached.drop 154)
      (PairLightPrepared5.rightRows.drop 154) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared5
end
