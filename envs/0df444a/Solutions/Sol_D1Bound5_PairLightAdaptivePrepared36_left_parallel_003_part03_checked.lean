-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.left_parallel_003_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:18.811934+00:00
-- url     : https://prove2.me/submissions/3cf17100-08c3-4eda-b565-55d7e6b6053f

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

/-- Original heads 322 through 333, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 322) (PairLightPrepared36.leftRows.drop 322) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared36
end
