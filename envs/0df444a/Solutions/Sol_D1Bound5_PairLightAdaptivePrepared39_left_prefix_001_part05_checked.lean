-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared39.left_prefix_001_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:08:25.076623+00:00
-- url     : https://prove2.me/submissions/ed90cdd7-161d-4e6e-8289-909b738fe018

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

/-- Original heads 217 through 232, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 16
      (PairLightPrepared39.leftCached.drop 217)
      (PairLightPrepared39.leftRows.drop 217) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared39
end
