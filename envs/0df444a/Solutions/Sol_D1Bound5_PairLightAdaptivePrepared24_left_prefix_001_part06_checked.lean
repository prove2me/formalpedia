-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared24.left_prefix_001_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:15:47.705783+00:00
-- url     : https://prove2.me/submissions/e07b1d75-49c5-422f-83ac-da082744d3d2

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

/-- Original heads 245 through 247, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 3
      (PairLightPrepared24.leftCached.drop 245)
      (PairLightPrepared24.leftRows.drop 245) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared24
end
