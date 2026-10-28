-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.left_parallel_002_part08_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:19:20.887605+00:00
-- url     : https://prove2.me/submissions/0e9ccec5-46f0-434a-ad55-27bd388e5b3e

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

/-- Original heads 298 through 309, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 298) (PairLightPrepared14.leftRows.drop 298) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared14
end
