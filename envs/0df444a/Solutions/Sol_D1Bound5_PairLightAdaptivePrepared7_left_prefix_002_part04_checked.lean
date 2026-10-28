-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared7.left_prefix_002_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:22:19.356835+00:00
-- url     : https://prove2.me/submissions/28e9b60a-a84d-4ae6-8394-a1a81f71668e

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 364 through 387, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 24
      (PairLightPrepared7.leftCached.drop 364)
      (PairLightPrepared7.leftRows.drop 364) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared7
end
