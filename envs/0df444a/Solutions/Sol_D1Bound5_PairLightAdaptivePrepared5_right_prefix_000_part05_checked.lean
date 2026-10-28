-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared5.right_prefix_000_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:26:25.422996+00:00
-- url     : https://prove2.me/submissions/d3468de1-eb9e-4964-b38f-aa4906ea150b

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

/-- Original heads 60 through 71, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 12
      (PairLightPrepared5.rightCached.drop 60)
      (PairLightPrepared5.rightRows.drop 60) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared5
end
