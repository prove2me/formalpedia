-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.right_parallel_003_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:32:26.108153+00:00
-- url     : https://prove2.me/submissions/577196e8-412a-4787-8f5e-26ad9810ed37

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

/-- Original heads 465 through 476, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 465) (PairLightPrepared14.rightRows.drop 465) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared14
end
