-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.left_parallel_001_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:39:59.136096+00:00
-- url     : https://prove2.me/submissions/3dd2e7eb-c223-43a9-8bc7-a4d53ac87d33

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

/-- Original heads 130 through 141, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 130) (PairLightPrepared28.leftRows.drop 130) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared28
end
