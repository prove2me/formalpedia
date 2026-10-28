-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.left_parallel_001_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:37:39.307991+00:00
-- url     : https://prove2.me/submissions/13fee6d0-57d9-45c6-b4f0-53b9925f9e4e

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

/-- Original heads 160 through 171, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 160) (PairLightPrepared14.leftRows.drop 160) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared14
end
