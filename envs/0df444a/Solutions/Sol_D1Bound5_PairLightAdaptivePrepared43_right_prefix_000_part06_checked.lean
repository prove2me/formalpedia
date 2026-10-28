-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared43.right_prefix_000_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:08:18.755661+00:00
-- url     : https://prove2.me/submissions/66b9d25c-c6eb-488e-8bc5-25b53ffb6cbc

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

/-- Original heads 72 through 83, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 12
      (PairLightPrepared43.rightCached.drop 72)
      (PairLightPrepared43.rightRows.drop 72) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared43
end
