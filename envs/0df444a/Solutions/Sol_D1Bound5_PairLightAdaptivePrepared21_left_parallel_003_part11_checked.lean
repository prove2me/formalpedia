-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.left_parallel_003_part11_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:28:02.626482+00:00
-- url     : https://prove2.me/submissions/5e2426b4-e654-4133-86c9-efa0b76c9f26

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 467 through 478, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 467) (PairLightPrepared21.leftRows.drop 467) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared21
end
