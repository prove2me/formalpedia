-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared43.right_prefix_001_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:10:36.534707+00:00
-- url     : https://prove2.me/submissions/84183e2d-3a8c-48f8-9091-216169a7d88d

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

/-- Original heads 128 through 139, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 12
      (PairLightPrepared43.rightCached.drop 128)
      (PairLightPrepared43.rightRows.drop 128) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared43
end
