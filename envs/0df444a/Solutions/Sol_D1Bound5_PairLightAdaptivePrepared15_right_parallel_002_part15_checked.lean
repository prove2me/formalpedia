-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part15_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:25:15.125973+00:00
-- url     : https://prove2.me/submissions/40015749-d6ad-4d38-83e8-9470003aaa45

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 394 through 405, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 394) (PairLightPrepared15.rightRows.drop 394) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared15
end
