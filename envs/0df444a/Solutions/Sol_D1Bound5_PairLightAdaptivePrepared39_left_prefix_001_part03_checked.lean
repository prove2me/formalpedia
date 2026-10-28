-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared39.left_prefix_001_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:53:10.598519+00:00
-- url     : https://prove2.me/submissions/9ecf4a63-b7e0-41b3-8848-c7ab729818ed

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

/-- Original heads 169 through 192, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.leftCached.drop 169)
      (PairLightPrepared39.leftRows.drop 169) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared39
end
