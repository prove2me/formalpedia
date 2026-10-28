-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.left_parallel_001_part07_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:22:04.151994+00:00
-- url     : https://prove2.me/submissions/7542675b-c5a6-4428-9ec2-118efc2a696a

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 160 through 166, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 7
      (PairLightPrepared36.leftCached.drop 160) (PairLightPrepared36.leftRows.drop 160) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared36
end
