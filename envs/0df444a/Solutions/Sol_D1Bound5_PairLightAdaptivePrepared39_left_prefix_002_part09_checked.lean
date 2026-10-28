-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared39.left_prefix_002_part09_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:39:04.265427+00:00
-- url     : https://prove2.me/submissions/50e67c55-7ff0-4f3d-9833-37a81efdbceb

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

/-- Original heads 449 through 457, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 9
      (PairLightPrepared39.leftCached.drop 449)
      (PairLightPrepared39.leftRows.drop 449) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared39
end
