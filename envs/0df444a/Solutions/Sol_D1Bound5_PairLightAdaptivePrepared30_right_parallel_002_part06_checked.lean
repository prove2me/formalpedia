-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared30.right_parallel_002_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:16:07.8508+00:00
-- url     : https://prove2.me/submissions/09d1624c-ac53-4780-83ff-53ec1fc34c83

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 286 through 297, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 286) (PairLightPrepared30.rightRows.drop 286) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared30
end
