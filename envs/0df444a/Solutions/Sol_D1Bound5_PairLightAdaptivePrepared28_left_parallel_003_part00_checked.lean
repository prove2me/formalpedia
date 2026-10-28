-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.left_parallel_003_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:21:39.109498+00:00
-- url     : https://prove2.me/submissions/d6391ff0-5eea-4653-baa0-65cc5d4cac77

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 335 through 346, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 335) (PairLightPrepared28.leftRows.drop 335) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared28
end
