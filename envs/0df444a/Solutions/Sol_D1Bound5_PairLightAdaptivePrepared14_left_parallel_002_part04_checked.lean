-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.left_parallel_002_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:29:49.319521+00:00
-- url     : https://prove2.me/submissions/51fb5ba0-99a4-45f1-960a-c4c4c6dce7fa

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 250 through 261, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 250) (PairLightPrepared14.leftRows.drop 250) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared14
end
