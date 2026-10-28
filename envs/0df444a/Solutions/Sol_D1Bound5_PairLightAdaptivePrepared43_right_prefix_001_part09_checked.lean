-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared43.right_prefix_001_part09_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:37:25.345543+00:00
-- url     : https://prove2.me/submissions/b88d6c08-bf47-48ac-a10d-0f0f0f8867bb

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

/-- Original heads 200 through 211, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 12
      (PairLightPrepared43.rightCached.drop 200)
      (PairLightPrepared43.rightRows.drop 200) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared43
end
