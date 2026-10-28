-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared43.left_prefix_001_part09_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:37:49.783802+00:00
-- url     : https://prove2.me/submissions/3a0e8530-ebd6-4203-833d-50bf2b0b4a0e

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 199 through 210, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 12
      (PairLightPrepared43.leftCached.drop 199)
      (PairLightPrepared43.leftRows.drop 199) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared43
end
