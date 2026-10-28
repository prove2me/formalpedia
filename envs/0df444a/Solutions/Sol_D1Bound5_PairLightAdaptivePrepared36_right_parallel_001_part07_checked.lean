-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.right_parallel_001_part07_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:35:27.203566+00:00
-- url     : https://prove2.me/submissions/dd7a93ef-59ac-44cb-b7a8-179d5a5f3273

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

/-- Original heads 160 through 166, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 7
      (PairLightPrepared36.rightCached.drop 160) (PairLightPrepared36.rightRows.drop 160) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared36
end
