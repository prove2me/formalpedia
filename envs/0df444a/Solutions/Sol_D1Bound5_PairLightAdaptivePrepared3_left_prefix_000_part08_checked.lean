-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared3.left_prefix_000_part08_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:45:37.271899+00:00
-- url     : https://prove2.me/submissions/9f2c1c58-fbab-4a90-bce8-e46c90597268

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 96 through 107, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 12
      (PairLightPrepared3.leftCached.drop 96)
      (PairLightPrepared3.leftRows.drop 96) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared3
end
