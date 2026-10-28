-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared19.left_prefix_002_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:48:46.855291+00:00
-- url     : https://prove2.me/submissions/8b4736a7-e409-4535-a1e8-a2522f5fa818

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 368 through 391, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.leftCached.drop 368)
      (PairLightPrepared19.leftRows.drop 368) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared19
end
