-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared39.right_pilot12_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:23:25.077823+00:00
-- url     : https://prove2.me/submissions/38f8d4aa-4771-402e-8a1f-46d8a862075a

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 0 through 11, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 12
      (PairLightPrepared39.rightCached.drop 0)
      (PairLightPrepared39.rightRows.drop 0) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared39
end
