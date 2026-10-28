-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared39.left_prefix_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:44:38.379081+00:00
-- url     : https://prove2.me/submissions/d7741fa0-9df1-475b-8cc0-29825c861429

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 48 through 59, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 12
      (PairLightPrepared39.leftCached.drop 48)
      (PairLightPrepared39.leftRows.drop 48) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared39
end
