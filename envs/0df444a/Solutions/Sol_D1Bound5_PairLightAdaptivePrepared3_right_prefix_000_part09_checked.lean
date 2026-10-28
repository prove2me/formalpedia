-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared3.right_prefix_000_part09_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:54:28.502761+00:00
-- url     : https://prove2.me/submissions/b16997ea-f257-41f7-998e-5d74d9ca0164

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3RightRows_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 108 through 110, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 3
      (PairLightPrepared3.rightCached.drop 108)
      (PairLightPrepared3.rightRows.drop 108) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared3
end
