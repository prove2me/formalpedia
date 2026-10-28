-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared5.left_prefix_001_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:14.845463+00:00
-- url     : https://prove2.me/submissions/092432f6-60bb-4831-b224-0267fdaa3c03

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 249 through 268, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 20
      (PairLightPrepared5.leftCached.drop 249)
      (PairLightPrepared5.leftRows.drop 249) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared5
end
