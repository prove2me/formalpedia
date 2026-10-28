-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared39.right_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:56.953656+00:00
-- url     : https://prove2.me/submissions/860a1861-0f58-4f2e-828d-5f547091c94e

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

/-- Original heads 122 through 145, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.rightCached.drop 122)
      (PairLightPrepared39.rightRows.drop 122) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared39
end
