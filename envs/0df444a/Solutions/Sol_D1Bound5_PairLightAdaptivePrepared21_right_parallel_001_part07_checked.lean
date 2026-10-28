-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.right_parallel_001_part07_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:11.641348+00:00
-- url     : https://prove2.me/submissions/475108b3-fdd6-4d88-99fe-1eb7e3315557

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 166 through 177, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.rightCached.drop 166) (PairLightPrepared21.rightRows.drop 166) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared21
end
