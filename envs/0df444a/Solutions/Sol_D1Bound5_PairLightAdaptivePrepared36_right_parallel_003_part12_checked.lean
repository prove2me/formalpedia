-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part12_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:57:06.761496+00:00
-- url     : https://prove2.me/submissions/e73c478c-986e-4117-a70d-cd3a0ad0369f

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 431 through 442, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 431) (PairLightPrepared36.rightRows.drop 431) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared36
end
