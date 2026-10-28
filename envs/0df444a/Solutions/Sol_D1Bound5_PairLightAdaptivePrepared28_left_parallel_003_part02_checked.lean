-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.left_parallel_003_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:49:22.243365+00:00
-- url     : https://prove2.me/submissions/3c818d51-0d2c-443f-8c0f-222964cdaa89

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

/-- Original heads 359 through 370, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 359) (PairLightPrepared28.leftRows.drop 359) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared28
end
