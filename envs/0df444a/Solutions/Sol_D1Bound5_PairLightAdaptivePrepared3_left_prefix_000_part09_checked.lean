-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared3.left_prefix_000_part09_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:23:43.403981+00:00
-- url     : https://prove2.me/submissions/3219b740-1ef9-4aa5-ba53-eb1dd46f71a3

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 108 through 111, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 4
      (PairLightPrepared3.leftCached.drop 108)
      (PairLightPrepared3.leftRows.drop 108) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared3
end
