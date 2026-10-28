-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared19.left_prefix_000_part08_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:39:05.03068+00:00
-- url     : https://prove2.me/submissions/e3c7fd90-4853-4753-982b-cbb91cf2deb0

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

/-- Original heads 96 through 100, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 5
      (PairLightPrepared19.leftCached.drop 96)
      (PairLightPrepared19.leftRows.drop 96) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared19
end
