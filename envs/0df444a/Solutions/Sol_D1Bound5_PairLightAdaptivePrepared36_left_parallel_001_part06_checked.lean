-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.left_parallel_001_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:15:31.303252+00:00
-- url     : https://prove2.me/submissions/edd62998-5f26-4ef5-bdfe-1cfd7a7d219e

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

/-- Original heads 148 through 159, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 148) (PairLightPrepared36.leftRows.drop 148) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared36
end
