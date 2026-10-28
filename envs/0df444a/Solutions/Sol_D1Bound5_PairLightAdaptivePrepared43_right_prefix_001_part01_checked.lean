-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared43.right_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:33:05.023992+00:00
-- url     : https://prove2.me/submissions/ab8ca73c-c10a-4752-b872-82aebe54fc92

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Right_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 104 through 115, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 12
      (PairLightPrepared43.rightCached.drop 104)
      (PairLightPrepared43.rightRows.drop 104) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared43
end
