-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.right_parallel_002_part07_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:21:54.962472+00:00
-- url     : https://prove2.me/submissions/b5e3abfb-c8f4-4350-a439-d10b09390011

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

/-- Original heads 251 through 262, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 251) (PairLightPrepared36.rightRows.drop 251) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared36
end
