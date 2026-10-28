-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part20_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:16:34.104488+00:00
-- url     : https://prove2.me/submissions/13a08eaa-2958-450f-8549-30aa50a01d87

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 526 through 537, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 526) (PairLightPrepared36.leftRows.drop 526) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared36
end
