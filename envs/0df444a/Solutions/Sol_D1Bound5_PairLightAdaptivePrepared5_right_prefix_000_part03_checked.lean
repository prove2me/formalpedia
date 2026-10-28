-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared5.right_prefix_000_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:58:28.76199+00:00
-- url     : https://prove2.me/submissions/7082fc6b-b6e2-4919-a2fc-114716f20b63

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 36 through 47, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 12
      (PairLightPrepared5.rightCached.drop 36)
      (PairLightPrepared5.rightRows.drop 36) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared5
end
