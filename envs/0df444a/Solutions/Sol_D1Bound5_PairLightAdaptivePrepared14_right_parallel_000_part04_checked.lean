-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.right_parallel_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:49:48.235004+00:00
-- url     : https://prove2.me/submissions/7bfc3e60-280e-437f-bb8f-8877c994e293

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 48 through 59, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 48) (PairLightPrepared14.rightRows.drop 48) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared14
end
