-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared19.left_prefix_002_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:07.418261+00:00
-- url     : https://prove2.me/submissions/f114f4db-aef7-4383-97b0-58d35d04c16d

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 320 through 343, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.leftCached.drop 320)
      (PairLightPrepared19.leftRows.drop 320) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared19
end
