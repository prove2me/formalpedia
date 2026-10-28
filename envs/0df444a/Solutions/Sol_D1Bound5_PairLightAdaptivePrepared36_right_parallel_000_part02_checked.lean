-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.right_parallel_000_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:10:29.382198+00:00
-- url     : https://prove2.me/submissions/c35c85fc-f7ca-44de-a62a-a4f74f7c11cc

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

/-- Original heads 24 through 35, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 24) (PairLightPrepared36.rightRows.drop 24) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared36
end
