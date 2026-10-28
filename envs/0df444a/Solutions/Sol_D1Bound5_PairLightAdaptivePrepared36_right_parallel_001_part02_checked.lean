-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.right_parallel_001_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:50:54.764761+00:00
-- url     : https://prove2.me/submissions/6baabc26-2d13-4cae-a3a7-c2949399c6a9

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 100 through 111, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 100) (PairLightPrepared36.rightRows.drop 100) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared36
end
