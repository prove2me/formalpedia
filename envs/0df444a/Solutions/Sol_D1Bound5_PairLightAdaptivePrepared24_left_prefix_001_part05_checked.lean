-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared24.left_prefix_001_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:38:45.883871+00:00
-- url     : https://prove2.me/submissions/57ed73d9-eb7b-4a71-8cd3-7382c8f95d61

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 221 through 244, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.leftCached.drop 221)
      (PairLightPrepared24.leftRows.drop 221) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared24
end
